# This is a program to compute connected and disconnected Hurwitz
# numbers. The two main routines are Z(g, d, A) which computes
# disconnected ones, and connHurwitz() which computes connected ones.

# There appears to be a fundamental limitation to this program due to
# Maple's internal memory management. The recursive function
# subparinternal() ends up producing lists that can be quite long; at
# somewhere around a length of 200 elements, Maple decides to quit and
# suggest using the Array data type. While I would be thrilled to do
# this, there is the issue that an Array must be 'rectangular'
# i.e. n_1 x n_2 x ... x n_k, whereas my lists are simply lists of
# lists, not all of the same length.

# Note also that the partitions must be in increasing order i.e. you
# must enter [1,2,3] instead of [3,2,1] or, heaven forfend, [3,1,2],
# or Maple will object that the given partition is not a partition of
# the right number.

#####################################################################
#
# These first two functions are to compute the disconnected Hurwitz
# numbers; they are much simpler to compute.
#
#####################################################################

# int auto(int[] a)
# returns the number of automorphisms of a permutation a.
with(combinat);
auto := proc (a)
local d, k, i, A, j, prdct;
d := sum(a[i], i = 1 .. nops(a));
for k to d do A[k] := 0;
    for i to nops(a) do
        if a[i] = k then
            A[k] := A[k]+1;
        end if;
    end do;
end do;
prdct := 1;
for j to d do
    prdct := prdct*factorial(A[j])*j^A[j];
end do;
return prdct
end proc;

# int Z(int g, int d, int[][] A)
# returns the disconnected Hurwitz number. See e.g. Fulton and Harris,
# Representation Theory.

Z := proc (g, d, A)
local parts, p, r, Q, prod, j, b;
with(combinat);
parts := partition(d);
p := nops(parts);
r := nops(A);
Q := 0;
# print(d, A, parts);
for j to p do
    prod := 1;
    for b to r do
        prod := prod*Chi(parts[j], A[b])*factorial(d)/(auto(A[b])*Chi(parts[j], parts[1]));
    end do;
    Q := Q+prod*(factorial(d)/Chi(parts[j], parts[1]))^(2*g-2);
end do;
end proc;

######################################################################
#
# This here is the beast. This is what does all the hard work, and it
# is likely the largest bottleneck; I suppose the fact that it has to
# do polynomial computations with a very large number of variables
# doesn't help, but I don't think that it can be made much better.
#
######################################################################

# int connHurwitz(int g, int d, int[][] A)
# This should produce the number of degree d connected Hurwitz covers of a
# genus g curve ramified over nops(A) points with specified ramification
# given by A. This is done by taking the formal power series generated
# by makeZseries, takign its logarithm and looking at specific
# coefficients of that.

connHurwitz := proc (g::integer, d::integer, A_input::list)
local vars, r, j, i, k, Zseries, R, A;
local  monomial, coeff_list, monomial_list;
local cover_genus;

# Just a quick sanity check...

A := A_input;

R:= nops(A);

if R <> 0 then
    for r to R do
        if size(A[r]) <> d then
            printf("\n The partition %d is not a partition of %d.\n", r, d);
            return -1;
        end if;
    end do;
else
    # This is just in case no ramification is specified, it adds a
    # single unramified point.
    A := [[seq(1,r=1..d)]];
    R := 1;
end if;
vars := [];

# This is just to compute and display the genus of the covering curve,
# as a bit of a sanity check.

cover_genus := d * (g - 1 + 1/2 * nops(A)) - 1/2 * add(nops(A[k]),k=1..nops(A)) + 1;

if cover_genus < 0 then
    printf("\n There are no connected curves with this ramification data. (Genus < 0)\n\n");
    return;
else
    printf("\n The number of genus %a curves of degree %d is\n\n", cover_genus, d);
end if;

# We quickly make a list of all the variables that might show up in
# our expression.

for r to R do
    for j to d+1 do
        vars := [op(vars), z[r][j]];
    end do;
end do;

# This little bit here just creates the monomial that corresponds to
# the term we want.

monomial :=1;

for r to R do
    for j to d+1 do
        for i to nops(A[r]) do
            if A[r][i] = j then
                #new bit; this feels somehow redundant though.
                monomial := monomial * z[r][j];
                #end new bit.
            end if;
        end do;
    end do;
end do;

# The way this works is that we first generate a truncated generating
# series whose coefficients will be our Hurwitz numbers. This function
# actually generates each of the truncations, and returns an array so
# that the i-th term is the degree i truncation.

Zseries := makeRestrictedZSeries(g, A, d);

# Next, we manually use the Taylor expansion of the logarithm function
# truncated at the appropriate degree; we use each of the truncations
# from the list Zseries so as to minimize the number of computations
# required. As the result is a polynomial (if in many, many
# variables), we can simply use the Maple function coeffs() to
# determine the coefficient we care about.

coeff_list := [coeffs(collect(-sum(1/k * (-Zseries[d-k+1])^k, k=1..d),vars,'distributed'),vars,'monomial_list')];

monomial_list := [monomial_list];

# This last bit is just to see if our coefficient actually turns
# up. coeffs() fills the list monomial_list with a list of all
# variables that occur in the given expression, and so we just need to
# see if the one that we want (found earlier) shows up in that
# list. Otherwise we return 0 (as the coefficient is then zero).

for i from 1 to nops(monomial_list) do
if monomial_list[i] = monomial then return coeff_list[i]; end if;
end do;

return 0;
end proc;

####################################################################
#
# int connHurw(g::integer, d::integer, A_input::list)
#
# This is an abbreviated form for when all we intend to give are 1, 2,
# or 4 as inputs. A will then consist of a list [n_1, n_2, n_4], which
# will suffice for everything that I do.
#
####################################################################

connHurw := proc(g::integer, d::integer, A_input::list)
local A, k, i;

A := [];

for i from 1 to nops(A_input) do
    A := [op(A),[seq(1, k=1..A_input[i][1]), seq(2, k=1..A_input[i][2]), seq(4,k=1..A_input[i][3])]];
end do;

connHurwitz(g,d,A);
end proc;

# And this is even simpler if I don't intend to use any 4s. I'm just
# being lazy at this point.

connHurwS := proc(g::integer, d::integer, A_input::list)
local A, k, i;

A:=[];

for i from 1 to nops(A_input) do
    A := [op(A),[seq(1, k=1..A_input[i][1]), seq(2, k=1..A_input[i][2])]];
end do;

connHurwitz(g,d,A);
end proc;

# This is another one: it takes as input the arrays [n_1, n_2, k] which
# represents n_1 1s, n_2 2s, and a lonely integer k of whatever number
# I like.

connHurwk := proc(g::integer, d::integer, A_input::list)
local A, k, i;

A := [];

for i from 1 to nops(A_input) do
    if nops(A_input[i]) = 3 then
        A := [op(A), [seq(1, k=1..A_input[i][1]), seq(2, k=1..A_input[i][2]), A_input[i][3]]];
    elif nops(A_input[i]) = 2 then
        A := [op(A),[seq(1, k=1..A_input[i][1]), seq(2, k=1..A_input[i][2])]];
    else
        return -1;
    end if;
end do;

connHurwitz(g,d,A);
end proc;

#int size(int[] A)
# This simply returns the size |A| of a partition A. Seems useful to
# have it as a separate function...
size := proc (A)
return sum(A[i], i = 1 .. nops(A));
end proc;

####################################################################
#
# The next few routines are for manipulation of partitions to produce
# lists of subpartitions.
#
####################################################################

# This routine takes as input a partition (taken to be a list A) and
# an integer n. It then recursively finds all sub-partitions of A
# which are partitions of n.

# This seems to be problematic in its implementation, however, in that
# using lists in Maple is very inefficient--a better method would be
# to modify this so that it uses the Vector data type instead, although
# at the moment I am not 100% certain how to do what this does with
# that data type...

subparinternal := proc (A, n)
local recur, recurb, i;
if size(A) < n then
    return -1;
end if;
recur := [];
if A[1] = n then
    recur := thisproc([op(2 .. nops(A), A)], n);
    #print(A, n, nops(recur));
    if recur = -1 then
        return [[n]];
    else
        return [op(recur), [n]];
    end if;
elif A[1] < n then
    recur := thisproc([op(2 .. nops(A), A)], n-A[1]);
    #print(A, n, nops(recur));
    if recur = -1 then
        return thisproc([op(2 .. nops(A), A)], n);
    else
        for i to nops(recur) do
            recur[i] := [A[1], op(recur[i])];
        end do;
        recurb := thisproc([op(2 .. nops(A), A)], n);
        #print(A, n, nops(recurb));
        if recurb = -1 then
            return recur;
        else
            return [op(recur), op(recurb)];
        end if;
    end if;
else
    return thisproc([op(2 .. nops(A), A)], n);
end if;
end proc;

# int check_shortcut(A::list)
# This is a routine to check whether or not a partition consists
# solely of 1s and 2s; in such a case, subparinternal tends to get
# congested, and we should simply be able to figure out the answer
# manually, so this seems to be a good simplification.

check_shortcut := proc(A::list)
local i, two_count;

two_count := 0;
for i from 1 to nops(A) do
    if A[i] > 2 then
        return -1;
    elif A[i] = 2 then
        two_count := two_count + 1;
    end if;
end do;

return two_count;
end proc;

# I will extend this in the following way: As I will care about cases
# where we have one integer greater than 2 showing up, it will now do
# the following: First, check if the right-most two integers are an
# integer greater than 2 and a 1 or a 2. If it is, then it does a
# special form. If it is 2s and 1s, do the usual shortcut. Anything
# else, and it goes the long road.

check_shortcut_B := proc(A::list)
local i, two_count;

# First check to see if the rest of the string is ok, and tell us how
# many 2s there are.
two_count := check_shortcut([op(1..(nops(A)-1),A)]);

# We know that check_shortcut() failed, so return the erroneous digit
# and the number of 2s.
if two_count <> -1 then
    return two_count;
end if;

# Otherwise all hell breaks loose.
return -1;
end proc;

# list subpar_shortcut(d::integer, n::integer, num_twos::integer)
# This simply takes advantage of the fact that if our partition of d
# consists solely of 1s and 2s, it is very easy to just write down all
# possible subpartitions totally to a particular number, n.

subpar_shortcut := proc(d::integer, n::integer, num_twos::integer)
local output, j, k, num_ones;
# check silly error bounds
if 2 * num_twos > d then
    return -1;
elif 2 * num_twos = d and type(n,odd) then
    return -1;
elif n > d then
    return -1;
end if;

output := [];
num_ones := d - 2 * num_twos;

for j from 0 to min(floor(n/2),num_twos) do
    if n - 2 * j <= num_ones then
        output := [op(output),[seq(1,k=1..(n-2*j)),seq(2,k=1..j)]];
    end if;
end do;

return output;

end proc;

# int[][] subpar(int[] A, int n)
# This returns a distinct list of all subpartitions of A whose length
# is n. It does this by calling the previous function to generate a
# non-distinct lists, and then runs through it inefficiently to remove duplicates.

subpar := proc (A, n)
local temp, i, j, output, match, A_short;

# We should first check if this partition consists only of 1s and 2s.
i := check_shortcut(A);

if i <> -1 then
# return the appropriate list of partitions
    return subpar_shortcut(size(A), n, i);
end if;

# Try again for the second shortcut. That is, partitions of the form
# [1, ..., 1,2, ... ,2, k] for some integer k are not that hard to
# deal with either, and they come up often enough it seems
# worthwhile. It will mean that I can do longer partitions than I
# could before.

i := check_shortcut_B(A);

if i <> -1 then
    # First, make a shorter A removing the last term.
    A_short := [op(1..(nops(A)-1), A)];


    # Next, use this to generate partitions of n with i 2s.
    output := subpar_shortcut(size(A_short), n, i);

    if output = -1 then
        output := [];
    end if;

    # Lastly, add on those terms coming from the last term.

    if n >= A[-1] then
        temp := subpar_shortcut(size(A_short),n - A[-1], i);
        if temp <> -1 then
            for j from 1 to nops(temp) do
                temp[j] := [op(temp[j]), A[-1]];
            end do;
        else
            temp := [];
        end if;
    else
        # In this case, the last term is larger than n, and so it is
        # not possible for it to contribute.
        temp := [];
    end if;


    # And put both of these together.
    output := [op(output), op(temp)];


    # We now need to check to see that we found any matches at
    # all. It's possible that either previous option failed to return
    # matches, so we have to check for this.
    if nops(output) > 0 then
        return output;
    end if;

    return -1;
end if;

# Otherwise, use the recursive internal one which produces a list
# (with repetitions), and then remove the repetitions.

temp := subparinternal(A, n);
if temp = -1 then
    return -1;
else
    output := [];
    for i to nops(temp) do
        match := 0;
        for j to nops(output) do
            if output[j] = temp[i] then
                match := 1;
            end if;
        end do;
        if match <> 1 then
            output := [op(output), temp[i]];
        end if;
    end do;
end if;
return output;
end proc;

############################################################################
#
# These functions are what construct the truncated formal power
# series.
#
############################################################################

# These next two are based off of Jim's functions, but they should take
# into account the fact that we are restricting ourselves to
# subpartitions of the given partitions instead of allowing all possibilities.

# makeRestrictedZSeries(int g, int[][]A, int D)
# This function creates the formal power series whose coefficients are
# hurwitz numbers corresponding to the ramification data A (so we
# don't allow arbitrary ramification, but only ramification which
# could occur based on A, which is an array of partitions). The base
# genus is g, and we truncate the power series at degree D.

# The current form of this actually returns an array, whose degree i
# part is the degree i truncation of this function.

makeRestrictedZSeries := proc (g, A, DD)
local i, vars, output, pseries, k, prodterm, current_partitions, current_vars, j, r;

output := [];
pseries := 0;

for i to DD do
    vars := makeRestricteddp(A, i);
    if vars = -1 then
        # If we cannot have any terms of this degree, we should still
        # take that into account now that we are keeping all truncations.
        output:=[op(output), pseries];
    else
        for k to nops(vars) do
            prodterm := 1;
            current_partitions := vars[k];
            for r from 1 to nops(A) do
                current_vars := current_partitions[r];
                for j from 1 to nops(current_vars) do
                    prodterm := prodterm * z[r][current_vars[j]];
                end do;
            end do;
            pseries := pseries + prodterm * Z(g,i,current_partitions);
        end do;
        #do good things!
        output := [op(output), pseries];
    end if;
end do;
return output;
#return pseries;
end proc;

# makeRestricteddp(int[][]A, int d)
# int[][] A : A list of partitions of a fixed integer n
# int d : an integer (hopefully less than n). We are looking for
# subpartitions of the partitions in A that are partitions of d.
#
# This routine essentially returns a list of all the formal variables
# that we will need in our generating series; as opposed to looking at
# all partitions of the integers 1..n, we only look at those
# partitions that can be made up from parts of the given partitions.
#
# The output format is a list of nops(A)-tuples of partitions of the
# integer d, in the same order as the original list A.
#
# -1 is returned if it is not possible to make a partition of d out of
# any one of the partitions in the list A.

makeRestricteddp := proc (A, d)
local dp, partlist, T, i, listA;
dp := [];
partlist := [];
for i to nops(A) do
    listA := subpar(A[i], d);
    if listA = -1 then
        return -1;
    else
        partlist := [op(partlist), listA];
    end if;
end do;
T := cartprod(partlist);
while not T[finished] do
    dp := [op(dp), T[nextvalue]()];
end do;
end proc;

#########################################################################
#
# And now some quick examples.
#
#########################################################################

#connHurwitz(0,12,[[1,1,1,1,1,1,2,2,2],[2,2,2,2,2,2],[2,2,2,2,2,2],[2,2,2,2,2,2],[1,1,1,1,1,1,1,1,1,1,2]]);

# These first few should be counting the number of degree 2d+1
# unramified covers of an elliptic curve for d = 1, 2, 3, 4

connHurwitz(0,3,[[1,2],[1,2],[1,2],[1,2]]);
connHurwitz(0,5,[[1,2,2],[1,2,2],[1,2,2],[1,2,2]]);
connHurwitz(0,7,[[1,2,2,2],[1,2,2,2],[1,2,2,2],[1,2,2,2]]);
connHurwitz(0,9,[[1,2,2,2,2],[1,2,2,2,2],[1,2,2,2,2],[1,2,2,2,2]]);

# These should count the same for the even degrees, but there are
# subtleties in this case due to automorphisms and choice of
# ramification data.

connHurwitz(0,4,[[1,1,1,1],[2,2],[2,2],[2,2]]);
connHurwitz(0,4,[[1,1,2],[1,1,2],[2,2],[2,2]]);

connHurwitz(0,6,[[1,1,2,2],[1,1,2,2],[2,2,2],[2,2,2]]);

connHurwitz(0,8,[[1,1,1,1,2,2],[2,2,2,2],[2,2,2,2],[2,2,2,2]]);
connHurwitz(0,8,[[1,1,2,2,2],[1,1,2,2,2],[2,2,2,2],[2,2,2,2]]);
