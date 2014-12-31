An Agda implementation of the "maps" representation of lambda terms, as
described in:

>  Viewing λ-terms through maps  
>  Masahiko Sato, Randy Pollack, Helmut Schwichtenberg and Takafumi Sakurai  
>  Indagationes Mathematicae 24 (2013) 1073–1104  
>  <http://dx.doi.org/10.1016/j.indag.2013.08.003>

This is just the maps representation, but uses Agda's support for
induction-induction and recursion-recursion definitions to bypass the symbolic
expressions and obtain the representation directly.  Also, Agda's support for
irrelevance annotations makes the representation canonical: the proofs of the
orthogonality of two maps in the representation are marked as irrelevant,
which makes proofs of the divisibility relation, and hence the representation
of lambda terms, unique.
