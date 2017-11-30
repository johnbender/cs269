(*
Example program:

sum = 0;
for i in 1..2 do
  sum = sum + rand(0, 1)

Example program unrolled:

sum = 0;
sum = sum + rand(0, 1);
sum = sum + rand(0, 1)

Type derivation

sum = 0; ( sum : nat )

sum : nat    rand(0, 1) : dist uniform 0 1    iid sum rand(0, 1)
-----------------------------------------------------------------
sum + rand(0, 1) : dist uniform sum sum+1

sum : dist uniform sum sum+1     rand(0, 1) : dist uniform 0 1    sum rand(0, 1) : iid
--------------------------------------------------------------------------------------
sum + rand(0, 1) : dist conv ...



Definitions:

canon e D <=> e is the canonical expression representing a distribution

eg,
  canon rand(0,1) (dist uniform 0 1)
  canon (rand(0,1) * (b-a) + a) (dist uniform a b)

#V(v) = count of v in V

pdf_e(v) = #V(v)/|V|
  where V = { v' | e || v' } (multiset)
        |V| -> inf

pdf_e = pdf_e' <=> forall v, pdf_e(v) = pdf_e'(v)
pdf_e(v) = D(v) <=> canon ec D /\ pdf_ec(v) = pdf_e(v)

Transformation soundness:

if [[e]] = e' then pdf_e = pdf_e'


(1) Type soundness

if e : D and e || v then pdf_e(v) = D(v)


(2) Transformation type preservation

if [[e]] = e' and [[e]] : D then e' : D

Should be trivial in our setting since the transformation should simply replace
e with a canonical term of type D (the distribution expression). It's easy to
imagine less obvious transformations that would have to satisfy the same
property.

Together 1 and 2 imply, Transformation soundness

Example transformations

[[e]] = e
[[e]] = v = 0; for i..rand(1, inf) do v = e; v
[[rand(0,1) + rand(0,1)]] = irwinhall(2)

Computer algebra aided simplification

http://hakaru-dev.github.io/transforms/hk-maple/

*)
