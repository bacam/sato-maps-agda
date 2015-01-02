module maps where

import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming (subst to substeq)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to refll)
open import Relation.Nullary

-- Parameters are a type along with decidable equality
postulate 𝕏 : Set
postulate _=𝕏_ : (x y : 𝕏) -> (x ≡ y) ⊎ (x ≢ y)

-- Maps

data 𝕄+ : Set where
  one : 𝕄+
  inl : 𝕄+ -> 𝕄+
  inr : 𝕄+ -> 𝕄+
  cons : 𝕄+ -> 𝕄+ -> 𝕄+

data 𝕄 : Set where
  zero : 𝕄
  incl : 𝕄+ -> 𝕄

mapp : 𝕄 -> 𝕄 -> 𝕄
mapp    zero     zero  = zero
mapp (incl m)    zero  = incl (inl m)
mapp    zero  (incl n) = incl (inr n)
mapp (incl m) (incl n) = incl (cons m n)

data Mapp : 𝕄 -> 𝕄 -> 𝕄 -> Set where
  mappzz : Mapp zero zero zero
  mappiz : (m : 𝕄+) -> Mapp (incl m) zero (incl (inl m))
  mappzi : (n : 𝕄+) -> Mapp zero (incl n) (incl (inr n))
  mappii : (m : 𝕄+) -> (n : 𝕄+) -> Mapp (incl m) (incl n) (incl (cons m n))

mappview : forall {m n} -> Mapp m n (mapp m n)
mappview {zero} {zero} = mappzz
mappview {zero} {incl n} = mappzi n
mappview {incl m} {zero} = mappiz m
mappview {incl m} {incl n} = mappii m n


data _⊥_ : 𝕄 -> 𝕄 -> Set where
  zr : (m : 𝕄) -> m ⊥ zero
  zl : (n : 𝕄) -> zero ⊥ n
  ap : {m n m' n' : 𝕄} -> m ⊥ n -> m' ⊥ n' -> mapp m m' ⊥ mapp n n'

-- The proofs are orthogonality are not unique :(
-- We'll use irrelevance to get around this later
⊥notunique : ¬ ((m : 𝕄)(n : 𝕄)(p1 : m ⊥ n)(p2 : m ⊥ n) -> p1 ≡ p2)
⊥notunique f with f zero zero (zr zero) (zl zero)
⊥notunique f | ()

⊥notunique' : ¬ ((m : 𝕄)(n : 𝕄)(p1 : m ⊥ n)(p2 : m ⊥ n) -> p1 ≡ p2)
⊥notunique' f with f zero zero (zr zero) (ap (zl zero) (zl zero))
⊥notunique' f | ()

data _⊥_eq : 𝕄 -> 𝕄 -> Set where
  zr : (m n : 𝕄) -> n ≡ zero -> m ⊥ n eq
  zl : (m n : 𝕄) -> m ≡ zero -> m ⊥ n eq
  ap : {m n m' n' m'' n'' : 𝕄} -> m ⊥ n -> m' ⊥ n' -> m'' ≡ mapp m m' -> n'' ≡ mapp n n' -> m'' ⊥ n'' eq

⊥eq : {m n : 𝕄} -> m ⊥ n -> m ⊥ n eq
⊥eq (zr m) = zr m zero refl
⊥eq (zl n) = zl zero n refl
⊥eq (ap b b') = ap b b' refl refl

data _⊥_cases : 𝕄 -> 𝕄 -> Set where
  zz : zero ⊥ zero cases
  iz : (m : 𝕄+) -> incl m ⊥ zero cases
  zi : (n : 𝕄+) -> zero ⊥ incl n cases
  ll : (m : 𝕄+)(n : 𝕄+) -> incl (inl m) ⊥ incl (inl n) cases
  lr : (m : 𝕄+)(n : 𝕄+) -> incl (inl m) ⊥ incl (inr n) cases
  lc : (m : 𝕄+)(n1 n2 : 𝕄+) -> incl (inl m) ⊥ incl (cons n1 n2) cases
  rl : (m : 𝕄+)(n : 𝕄+) -> incl (inr m) ⊥ incl (inl n) cases
  rr : (m : 𝕄+)(n : 𝕄+) -> incl (inr m) ⊥ incl (inr n) cases
  rc : (m : 𝕄+)(n1 n2 : 𝕄+) -> incl (inr m) ⊥ incl (cons n1 n2) cases
  cl : (m1 m2 : 𝕄+)(n : 𝕄+) -> incl (cons m1 m2) ⊥ incl (inl n) cases
  cr : (m1 m2 : 𝕄+)(n : 𝕄+) -> incl (cons m1 m2) ⊥ incl (inr n) cases
  cc : (m1 m2 : 𝕄+)(n1 n2 : 𝕄+) -> incl (cons m1 m2) ⊥ incl (cons n1 n2) cases

⊥cases : {m n : 𝕄} -> m ⊥ n -> m ⊥ n cases
⊥cases (zr zero) = zz
⊥cases (zr (incl x)) = iz x
⊥cases (zl zero) = zz
⊥cases (zl (incl x)) = zi x
⊥cases (ap {zero} {zero} {zero} {zero} or or₁) = zz
⊥cases (ap {zero} {zero} {zero} {incl x} or or₁) = zi (inr x)
⊥cases (ap {zero} {zero} {incl x} {zero} or or₁) = iz (inr x)
⊥cases (ap {zero} {zero} {incl x} {incl x₁} or or₁) = rr x x₁
⊥cases (ap {zero} {incl x} {zero} {zero} or or₁) = zi (inl x)
⊥cases (ap {zero} {incl x} {zero} {incl x₁} or or₁) = zi (cons x x₁)
⊥cases (ap {zero} {incl x} {incl x₁} {zero} or or₁) = rl x₁ x
⊥cases (ap {zero} {incl x} {incl x₁} {incl x₂} or or₁) = rc x₁ x x₂
⊥cases (ap {incl x} {zero} {zero} {zero} or or₁) = iz (inl x)
⊥cases (ap {incl x} {zero} {zero} {incl x₁} or or₁) = lr x x₁
⊥cases (ap {incl x} {zero} {incl x₁} {zero} or or₁) = iz (cons x x₁)
⊥cases (ap {incl x} {zero} {incl x₁} {incl x₂} or or₁) = cr x x₁ x₂
⊥cases (ap {incl x} {incl x₁} {zero} {zero} or or₁) = ll x x₁
⊥cases (ap {incl x} {incl x₁} {zero} {incl x₂} or or₁) = lc x x₁ x₂
⊥cases (ap {incl x} {incl x₁} {incl x₂} {zero} or or₁) = cl x x₂ x₁
⊥cases (ap {incl x} {incl x₁} {incl x₂} {incl x₃} or or₁) = cc x x₂ x₁ x₃

mappeq0 : (m n m' n' : 𝕄) -> mapp m n ≡ mapp m' n' -> (m ≡ m') × (n ≡ n')
mappeq0 zero zero zero zero refl = refl , refl
mappeq0 zero zero zero (incl x) ()
mappeq0 zero (incl x) zero zero ()
mappeq0 zero (incl x) zero (incl .x) refl = refl , refl
mappeq0 zero zero (incl x) zero ()
mappeq0 zero zero (incl x) (incl x₁) ()
mappeq0 zero (incl x) (incl x₁) zero ()
mappeq0 zero (incl x) (incl x₁) (incl x₂) ()
mappeq0 (incl x) zero zero zero ()
mappeq0 (incl x) zero zero (incl x₁) ()
mappeq0 (incl x) zero (incl .x) zero refl = refl , refl
mappeq0 (incl x) zero (incl x₁) (incl x₂) ()
mappeq0 (incl x) (incl x₁) zero zero ()
mappeq0 (incl x) (incl x₁) zero (incl x₂) ()
mappeq0 (incl x) (incl x₁) (incl x₂) zero ()
mappeq0 (incl x) (incl x₁) (incl .x) (incl .x₁) refl = refl , refl

mappeqzero : (m n : 𝕄) -> mapp m n ≡ zero -> (m ≡ zero) × (n ≡ zero)
mappeqzero zero zero refl = refl , refl
mappeqzero zero (incl x) ()
mappeqzero (incl x) zero ()
mappeqzero (incl x) (incl x₁) ()

mappeql : {m n m' n' : 𝕄} -> mapp m n ≡ mapp m' n' -> m ≡ m'
mappeql {m}{n}{m'}{n'} e = proj₁ (mappeq0 m n m' n' e)

mappeqr : {m n m' n' : 𝕄} -> mapp m n ≡ mapp m' n' -> n ≡ n'
mappeqr {m}{n}{m'}{n'} e = proj₂ (mappeq0 m n m' n' e)

⊥eqsp : (m n m' n' : 𝕄) -> mapp m m' ⊥ mapp n n' eq -> (m ⊥ n) × (m' ⊥ n')
⊥eqsp m n m' n' (zr .(mapp m m') .(mapp n n') e) with mappeqzero n n' e
⊥eqsp m .zero m' .zero (zr .(mapp m m') .(mapp zero zero) e) | refl , refl = zr m , zr m'
⊥eqsp m n m' n' (zl .(mapp m m') .(mapp n n') e) with mappeqzero m m' e
⊥eqsp .zero n .zero n' (zl .(mapp zero zero) .(mapp n n') e) | refl , refl = zl n , zl n'
⊥eqsp m n m' n' (ap {m0}{n0}{m0'}{n0'} o1 o2 e1 e2)  with mappeq0 m m' m0 m0' e1 | mappeq0 n n' n0 n0' e2
⊥eqsp m n m' n' (ap o1 o2 e1 e2) | refl , refl | refl , refl = o1 , o2

⊥left : {m n m' n' : 𝕄} -> mapp m m' ⊥ mapp n n' -> m ⊥ n
⊥left b = proj₁ (⊥eqsp _ _ _ _ (⊥eq b))

⊥right : {m n m' n' : 𝕄} -> mapp m m' ⊥ mapp n n' -> m' ⊥ n'
⊥right {m}{n} b = proj₂ (⊥eqsp m n _ _ (⊥eq b))

sym⊥ : {m n : 𝕄} -> m ⊥ n -> n ⊥ m
sym⊥ (zr m) = zl m
sym⊥ (zl n) = zr n
sym⊥ (ap b b') = ap (sym⊥ b) (sym⊥ b')

one⊥onecases : {X : Set} -> .(incl one ⊥ incl one cases) -> X
one⊥onecases ()

one⊥one : {X : Set} -> .(incl one ⊥ incl one) -> X
one⊥one or = one⊥onecases (⊥cases or)

mutual
  data 𝕃 : Set where
    var  : 𝕏 -> 𝕃
    □    : 𝕃
    app  : 𝕃 -> 𝕃 -> 𝕃
    mask : (m : 𝕄)(M : 𝕃) -> m ∣ M -> 𝕃
  
  data _∣_ : 𝕄 -> 𝕃 -> Set where
    zv : (x : 𝕏) -> zero ∣ var x
    zb : zero ∣ □
    ob : (incl one) ∣ □
    dmapp : {m n : 𝕄}{M N : 𝕃} -> m ∣ M -> n ∣ N -> mapp m n ∣ app M N
    dmask : {m n : 𝕄}{N : 𝕃} -> m ∣ N -> (ndiv : n ∣ N) -> .(m ⊥ n) -> m ∣ mask n N ndiv

mutual
  dmappunique : forall {M N m0 m n} -> (y : m0 ∣ app M N) -> m0 ≡ mapp m n -> (d1 : m ∣ M) -> (d2 : n ∣ N) -> dmapp d1 d2 ≅ y
  dmappunique {M}{N}{._}{m'}{n'} (dmapp {m}{n} y y₁) e d1 d2 with mappeql {m}{n}{m'}{n'} e | mappeqr {m}{n}{m'}{n'} e
  dmappunique (dmapp y y₁) e d1 d2 | refl | refl with ∣unique d1 y | ∣unique d2 y₁
  dmappunique (dmapp y y₁) e .y .y₁ | refl | refl | refl | refl = refll

  ∣unique : forall {m M} -> (x y : m ∣ M) -> x ≡ y
  ∣unique (zv x) (zv .x) = refl
  ∣unique zb zb = refl
  ∣unique ob ob = refl
  ∣unique (dmapp x x₁) y with dmappunique y refl x x₁
  ∣unique (dmapp x x₁) .(dmapp x x₁) | refll = refl
  ∣unique (dmask x x₁ x₂) (dmask y .x₁ x₃) with ∣unique x y
  ∣unique (dmask x x₁ x₂) (dmask .x .x₁ x₃) | refl = refl

zeromask : (M : 𝕃) -> zero ∣ M
zeromask (var x)      = zv x
zeromask □            = zb
zeromask (app M N)    = dmapp (zeromask M) (zeromask N)
zeromask (mask m M d) = dmask (zeromask M) d (zl m)

mutual
  fill : {m : 𝕄}{M : 𝕃} -> m ∣ M -> 𝕃 -> 𝕃
  fill (zv x)             P = var x
  fill  zb                P = □
  fill  ob                P = P
  fill (dmapp d1 d2)      P = app (fill d1 P) (fill d2 P)
  fill (dmask {m}{n}{N} d1 d2 orth) P = mask n (fill d1 P) (fillok m d1 d2 orth)

  fillok : forall {n}{N}{P} -> (m : 𝕄) -> (d1 : m ∣ N) -> n ∣ N -> .(m ⊥ n) -> n ∣ fill d1 P
  fillok .zero (zv x) d2 or = d2
  fillok .zero zb d2 or = d2
  fillok .(incl one) ob zb or = zeromask _
  fillok .(incl one) ob ob or = one⊥one or
  fillok ._ (dmapp {m} d1 d2) (dmapp {m'} d3 d4) or = dmapp (fillok _ d1 d3 (⊥left or)) (fillok _ d2 d4 (⊥right {m}{m'} or))
  fillok m (dmask d1 d2 o1) (dmask d3 .d2 o2) or = dmask (fillok _ d1 d3 or) (fillok _ d1 d2 o1) o2

map : 𝕏 -> 𝕃 -> 𝕄
map x (var y) with x =𝕏 y
map x (var .x) | inj₁ refl = incl one
map x (var y)  | inj₂ _ = zero
map x □ = zero
map x (app M N) = mapp (map x M) (map x N)
map x (mask m M _) = map x M

mutual
  skel : 𝕏 -> 𝕃 -> 𝕃
  skel x (var y) with x =𝕏 y
  skel x (var .x) | inj₁ refl = □
  skel x (var y)  | inj₂ _    = var y
  skel x □ = □
  skel x (app M N) = app (skel x M) (skel x N)
  skel x (mask m M d) = mask m (skel x M) (skelok d)

  skelok : {x : 𝕏}{m : 𝕄}{M : 𝕃} -> m ∣ M -> m ∣ skel x M
  skelok (zv x₁) = zeromask _
  skelok zb = zb
  skelok ob = ob
  skelok (dmapp d1 d2) = dmapp (skelok d1) (skelok d2)
  skelok (dmask d1 d2 or) = dmask (skelok d1) (skelok d2) or

mapdiv⊥ : (x : 𝕏){m : 𝕄}{M : 𝕃} -> m ∣ M -> map x M ⊥ m
mapdiv⊥ x (zv y) with x =𝕏 y
mapdiv⊥ x (zv .x) | inj₁ refl = zr (incl one)
mapdiv⊥ x (zv y)  | inj₂ _    = zr zero
mapdiv⊥ x zb = zr zero
mapdiv⊥ x ob = zl (incl one)
mapdiv⊥ x (dmapp d d₁) = ap (mapdiv⊥ x d) (mapdiv⊥ x d₁)
mapdiv⊥ x (dmask d d₁ x₁) = mapdiv⊥ x d

mapskel : (x : 𝕏)(M : 𝕃) -> map x M ∣ skel x M
mapskel x (var y) with x =𝕏 y
mapskel x (var .x) | inj₁ refl = ob
mapskel x (var y)  | inj₂ _    = zv _
mapskel x □ = zb
mapskel x (app M N) = dmapp (mapskel x M) (mapskel x N)
mapskel x (mask m M d) = dmask (mapskel x M) (skelok d) (mapdiv⊥ x d)

masksubst : forall {m M M'} -> (d : m ∣ M)(d' : m ∣ M') -> M ≡ M' -> mask m M d ≡ mask m M' d'
masksubst d d' refl with ∣unique d d'
masksubst d .d refl | refl = refl

mapzeroskel : (x : 𝕏)(M : 𝕃) -> map x M ≡ zero -> skel x M ≡ M
mapzeroskel x (var y) e with x =𝕏 y
mapzeroskel x (var .x) () | inj₁ refl
mapzeroskel x (var y)  e | inj₂ _    = refl
mapzeroskel x □ e = refl
mapzeroskel x (app M N) e with mappeqzero (map x M) (map x N) e
mapzeroskel x (app M N) e | e1 , e2 with mapzeroskel x M e1 | mapzeroskel x N e2
mapzeroskel x (app M N) e | e1 , e2 | e3 | e4 = cong₂ app e3 e4
mapzeroskel x (mask m M d) e with mapzeroskel x M e
mapzeroskel x (mask m M d) e | e1 = masksubst _ _ e1

appinj : forall {M N M' N'} -> app M N ≡ app M' N' -> (M ≡ M') × (N ≡ N')
appinj refl = refl , refl

maskinj : forall {m M M' d d'} -> mask m M d ≡ mask m M' d' -> M ≡ M'
maskinj refl = refl

maskinj' : forall {m m' M M' d d'} -> mask m M d ≡ mask m' M' d' -> (m ≡ m') × (M ≡ M')
maskinj' refl = refl , refl

skelmapzero : (x : 𝕏)(M : 𝕃) -> skel x M ≡ M -> map x M ≡ zero
skelmapzero x (var y)  e with x =𝕏 y
skelmapzero x (var .x) () | inj₁ refl
skelmapzero x (var y)   e | inj₂ _    = refl
skelmapzero x □ e = refl
skelmapzero x (app M N) e with appinj e
skelmapzero x (app M N) e | e1 , e2 with skelmapzero x M e1 | skelmapzero x N e2
skelmapzero x (app M N) e | e1 , e2 | e3 | e4 = cong₂ mapp e3 e4
skelmapzero x (mask m M d) e = skelmapzero x M (maskinj e)

lam : 𝕏 -> 𝕃 -> 𝕃
lam x M = mask (map x M) (skel x M) (mapskel x M)

subst : 𝕃 -> 𝕏 -> 𝕃 -> 𝕃
subst M x N = fill (mapskel x M) N

-- The comment on 1081 that "if x occurs in M then the corresponding positions
-- in m must be 0" can be expressed by ∣ in the conclusion below:
substdiv : forall {m M} -> (x : 𝕏)(P : 𝕃) -> m ∣ M -> m ∣ subst M x P
substdiv {m}{M} x P d = fillok _ (mapskel x M) (skelok d) (mapdiv⊥ x d)


masksubst' : forall {m m' M M'} -> (d : m ∣ M)(d' : m' ∣ M') -> m ≡ m' -> M ≡ M' -> mask m M d ≡ mask m' M' d'
masksubst' d d' refl refl with ∣unique d d'
masksubst' d .d refl refl | refl = refl

mapskelinj : forall {x M N} -> map x M ≡ map x N -> skel x M ≡ skel x N -> M ≡ N
mapskelinj {x} {var y} e1 e2 with x =𝕏 y
mapskelinj {x} {var .x} {var y} e1 e2 | inj₁ refl with x =𝕏 y
mapskelinj {x} {var .x} {var .x} e1 e2 | inj₁ refl | inj₁ refl = refl
mapskelinj {x} {var .x} {var y} e1 () | inj₁ refl | inj₂ x₁
mapskelinj {x} {var .x} {□} () e2 | inj₁ refl
mapskelinj {x} {var .x} {app N N₁} e1 () | inj₁ refl
mapskelinj {x} {var .x} {mask m N x₁} e1 () | inj₁ refl
mapskelinj {x} {var y} {var z} e1 e2 | inj₂ x₁ with x =𝕏 z
mapskelinj {x} {var y} {var .x} e1 () | inj₂ x₂ | inj₁ refl
mapskelinj {x} {var y} {var z} e1 e2 | inj₂ x₂ | inj₂ x₁ = e2
mapskelinj {x} {var y} {□} e1 () | inj₂ x₁
mapskelinj {x} {var y} {app N N₁} e1 () | inj₂ x₁
mapskelinj {x} {var y} {mask m N x₂} e1 () | inj₂ x₁
mapskelinj {x} {M = □} {var y} e1 e2 with x =𝕏 y
mapskelinj {x} {□} {var .x} () e2 | inj₁ refl
mapskelinj {x} {□} {var y} e1 () | inj₂ x₁
mapskelinj {M = □} {□} e1 e2 = refl
mapskelinj {M = □} {app N N₁} e1 ()
mapskelinj {M = □} {mask m N x₁} e1 ()
mapskelinj {x} {M = app M N} {var y} e1 e2 with x =𝕏 y 
mapskelinj {x} {app M N} {var .x} e1 () | inj₁ refl
mapskelinj {x} {app M N} {var y} e1 () | inj₂ x₁
mapskelinj {M = app M N} {□} e1 ()
mapskelinj {x} {M = app M N} {app M' N'} e1 e2 with mappeq0 (map x M) (map x N) (map x M') (map x N') e1 | appinj e2
mapskelinj {M = app M N} {app M' N'} e1 e2 | e3 , e4 | e5 , e6 = cong₂ app (mapskelinj e3 e5) (mapskelinj e4 e6)
mapskelinj {M = app M N} {mask m N₁ x₁} e1 ()
mapskelinj {x}{M = mask m M x₁} {var y} e1 e2 with x =𝕏 y 
mapskelinj {x} {mask m M x₂} {var .x} e1 () | inj₁ refl
mapskelinj {x} {mask m M x₂} {var y} e1 () | inj₂ x₁
mapskelinj {M = mask m M x₁} {□} e1 ()
mapskelinj {M = mask m M x₁} {app N N₁} e1 ()
mapskelinj {M = mask m M x₁} {mask m₁ N x₂} e1 e2 with maskinj' e2
mapskelinj {M = mask m M x₁} {mask m₁ N x₂} e1 e2 | e3 , e4 = masksubst' _ _ e3 (mapskelinj e1 e4)

lamrightinj : forall {x M N} -> lam x M ≡ lam x N -> M ≡ N
lamrightinj e with maskinj' e
lamrightinj e | e1 , e2 = mapskelinj e1 e2

-- Prop 1

substvareq : (x : 𝕏)(P : 𝕃) -> subst (var x) x P ≡ P
substvareq x P with x =𝕏 x
substvareq x P | inj₁ refl = refl
substvareq x P | inj₂ e with e refl
substvareq x P | inj₂ e | ()

substvarneq : (x y : 𝕏)(P : 𝕃) -> x ≢ y -> subst (var y) x P ≡ var y
substvarneq x y n P with x =𝕏 y
substvarneq x y n P | inj₁ e with P e
substvarneq x y n P | inj₁ e | ()
substvarneq x y n P | inj₂ e = refl

substbox : (x : 𝕏)(P : 𝕃) -> subst □ x P ≡ □
substbox x P = refl

substapp : (x : 𝕏)(M N P : 𝕃) -> subst (app M N) x P ≡ app (subst M x P) (subst N x P)
substapp x M N P = refl

substmask : (x : 𝕏)(m : 𝕄)(M P : 𝕃)(d : m ∣ M) -> subst (mask m M d) x P ≡ mask m (subst M x P) (substdiv x P d)
substmask x m M P d = refl

_♯_ : 𝕏 -> 𝕃 -> Set
x ♯ var y with x =𝕏 y
x ♯ var .x | inj₁ refl = Data.Empty.⊥
x ♯ var y | inj₂ _ = ⊤
x ♯ □ = ⊤
x ♯ app M N = (x ♯ M) × (x ♯ N)
x ♯ mask m M _ = x ♯ M

mapskelzero : (x : 𝕏)(M : 𝕃) -> map x (skel x M) ≡ zero
mapskelzero x (var y) with x =𝕏 y
mapskelzero x (var .x) | inj₁ refl = refl
-- Do I really need to do this twice?
mapskelzero x (var y) | inj₂ e with x =𝕏 y
mapskelzero x (var y) | inj₂ e | inj₁ e' with e e'
mapskelzero x (var y) | inj₂ e | inj₁ e' | ()
mapskelzero x (var y) | inj₂ e | inj₂ _ = refl
mapskelzero x □ = refl
mapskelzero x (app M N) with mapskelzero x M | mapskelzero x N
mapskelzero x (app M N) | e1 | e2 = cong₂ mapp e1 e2
mapskelzero x (mask m M d) = mapskelzero x M

skelidemp : (x : 𝕏)(M : 𝕃) -> skel x (skel x M) ≡ skel x M
skelidemp x M = mapzeroskel x (skel x M) (mapskelzero x M)

dmappinv : (m : 𝕄)(M N : 𝕃) -> (d : m ∣ app M N) -> Σ 𝕄 \m1 -> Σ 𝕄 \m2 -> Σ (m1 ∣ M) \d1 -> Σ (m2 ∣ N) \d2 -> (mapp m1 m2 ≡ m) × (d ≅ dmapp {m1}{m2}{M}{N} d1 d2)
dmappinv ._ M N (dmapp {m}{n} d1 d2) = m , (n , (d1 , (d2 , (refl , refll))))

dmappzero : (M N : 𝕃) -> (d : zero ∣ app M N) -> Σ (zero ∣ M) \d1 -> Σ (zero ∣ N) \d2 -> d ≅ dmapp {zero}{zero}{M}{N} d1 d2
dmappzero M N d with dmappinv zero M N d
dmappzero M N d | m1 , (m2 , (d1 , (d2 , (e1 , e2)))) with mappeqzero m1 m2 e1
dmappzero M N d | .zero , (.zero , (d1 , (d2 , (e1 , e2)))) | refl , refl = d1 , (d2 , e2)

fillzero : (M P : 𝕃)(d : zero ∣ M) -> fill {zero} d P ≡ M
fillzero (var x) P (zv .x) = refl
fillzero □ P zb = refl
fillzero (app M N) P d with dmappzero M N d
fillzero (app M N) P .(dmapp d1 d2) | d1 , (d2 , refll) = cong₂ app (fillzero M P d1) (fillzero N P d2)
fillzero (mask m M x) P (dmask d .x or) with fillzero M P d
fillzero (mask m M d1) P (dmask d .d1 or) | e = masksubst _ _ e
  

fillzeroeq : (m : 𝕄)(M M' P : 𝕃)(d : m ∣ M') -> m ≡ zero -> M' ≡ M -> fill d P ≡ M
fillzeroeq .zero M .M P d refl refl = fillzero M P d

diveq : forall {x M} -> map x M ≡ zero -> map x M ∣ M
diveq {x}{M} e = substeq (\m -> m ∣ M) (sym e) (zeromask _)

substskel : (x : 𝕏)(M P : 𝕃) -> subst (skel x M) x P ≡ skel x M
substskel x M P with mapskelzero x M
substskel x M P | e =  fillzeroeq _ _ _ P (mapskel x (skel x M)) e (skelidemp x M) 

substlameq : (x : 𝕏)(M P : 𝕃) -> subst (lam x M) x P ≡ lam x M
substlameq x M P with substskel x M P
substlameq x M P | e = masksubst _ _ e

mappzero : {m n : 𝕄} -> m ≡ zero -> n ≡ zero -> mapp m n ≡ zero
mappzero refl refl = refl

freshmap : (x : 𝕏)(M : 𝕃) -> x ♯ M -> map x M ≡ zero
freshmap x (var y) sh with x =𝕏 y
freshmap x (var .x) () | inj₁ refl
freshmap x (var y) sh | inj₂ _ = refl
freshmap x □ sh = refl
freshmap x (app M N) (fr1 , fr2) with freshmap x M fr1 | freshmap x N fr2
freshmap x (app M N) (fr1 , fr2) | e1 | e2 = mappzero e1 e2
freshmap x (mask m M _) fr = freshmap x M fr

substfresh : (x : 𝕏)(M P : 𝕃) -> x ♯ M -> subst M x P ≡ M
substfresh x M P fr = fillzeroeq _ _ (skel x M) P (mapskel x M) (freshmap x M fr) (mapzeroskel x M (freshmap x M fr))

freshskel : (x y : 𝕏)(M : 𝕃) -> x ♯ M -> x ♯ skel y M
freshskel x y (var z) fr with y =𝕏 z
freshskel x y (var .y) fr | inj₁ refl = tt
freshskel x y (var z) fr | inj₂ p = fr
freshskel x y □ fr = tt
freshskel x y (app M N) (fr₁ , fr₂) = freshskel x y M fr₁ , freshskel x y N fr₂
freshskel x y (mask m M _) fr = freshskel x y M fr

substlamfr : (x y : 𝕏)(M P : 𝕃) -> x ♯ M -> subst (lam y M) x P ≡ lam y M
substlamfr x y M P fr = substfresh x (lam y M) P (freshskel x y M fr)

-- typo in the paper
strange : (x y z : 𝕏) -> x ≢ y -> y ≢ z -> ¬ ((M : 𝕃) -> lam y M ≡ lam z (subst M x (var z)))
strange x y z n1 n2 p with p (var y)
strange x y z n1 n2 _ | q with y =𝕏 y | x =𝕏 y
strange x .x z n1 n2 _ | q | inj₁ refl | inj₁ refl with n1 refl
strange x .x z n1 n2 _ | q | inj₁ refl | inj₁ refl | ()
strange x y z n1 n2 _ | q | inj₁ refl | inj₂ x₁ with z =𝕏 y
strange x₁ y .y n1 n2 p | q | inj₁ refl | inj₂ x₂ | inj₁ refl with n2 refl
strange x₁ y .y n1 n2 p | q | inj₁ refl | inj₂ x₂ | inj₁ refl | ()
strange x₁ y z n1 n2 p | () | inj₁ refl | inj₂ x₂ | inj₂ x 
strange x y z n1 n2 _ | q | inj₂ x₁ | _ with x₁ refl
strange x y z n1 n2 _ | q | inj₂ x₁ | _ | ()

alphaskel : (y z : 𝕏) -> y ≢ z -> (M : 𝕃) -> z ♯ M -> skel y M ≡ skel z (subst M y (var z))
alphaskel y z ne (var x) fr with x =𝕏 y | y =𝕏 x
alphaskel y z ne (var .y) fr | inj₁ refl | inj₁ refl with z =𝕏 z
alphaskel y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₁ refl = refl
alphaskel y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₂ x with x refl
alphaskel y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₂ x | ()
alphaskel y z ne (var .y) fr | inj₁ refl | inj₂ x₂ with x₂ refl
alphaskel y z ne (var .y) fr | inj₁ refl | inj₂ x₂ | ()
alphaskel y z ne (var .y) fr | inj₂ x₁ | inj₁ refl with z =𝕏 z
alphaskel y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₁ refl = refl
alphaskel y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₂ x with x refl
alphaskel y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₂ x | ()
alphaskel y z ne (var x) fr | inj₂ x₁ | inj₂ x₂ with z =𝕏 x
alphaskel y x ne (var .x) () | inj₂ x₂ | inj₂ x₃ | inj₁ refl
alphaskel y z ne (var x) fr | inj₂ x₂ | inj₂ x₃ | inj₂ x₁ = refl
alphaskel y z ne □ fr = refl
alphaskel y z ne (app M N) (fr1 , fr2) with alphaskel y z ne M fr1 | alphaskel y z ne N fr2
alphaskel y z ne (app M N) (fr1 , fr2) | e1 | e2 = cong₂ app e1 e2
alphaskel y z ne (mask m M d) fr = masksubst (skelok d) (skelok (fillok (map y M) (mapskel y M) (skelok d) (mapdiv⊥ y d))) (alphaskel y z ne M fr)

alphamap : (y z : 𝕏) -> y ≢ z -> (M : 𝕃) -> z ♯ M -> map y M ≡ map z (subst M y (var z))
alphamap y z ne (var x) fr with x =𝕏 y | y =𝕏 x
alphamap y z ne (var .y) fr | inj₁ refl | inj₁ refl with z =𝕏 z
alphamap y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₁ refl = refl
alphamap y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₂ x with x refl
alphamap y z ne (var .y) fr | inj₁ refl | inj₁ refl | inj₂ x | ()
alphamap y z ne (var .y) fr | inj₁ refl | inj₂ x₂ with x₂ refl
alphamap y z ne (var .y) fr | inj₁ refl | inj₂ x₂ | ()
alphamap y z ne (var .y) fr | inj₂ x₁ | inj₁ refl with z =𝕏 z
alphamap y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₁ refl = refl
alphamap y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₂ x with x refl
alphamap y z ne (var .y) fr | inj₂ x₁ | inj₁ refl | inj₂ x | ()
alphamap y z ne (var x) fr | inj₂ x₁ | inj₂ x₂ with z =𝕏 x
alphamap y x ne (var .x) () | inj₂ x₂ | inj₂ x₃ | inj₁ refl
alphamap y z ne (var x) fr | inj₂ x₂ | inj₂ x₃ | inj₂ x₁ = refl
alphamap y z ne □ fr = refl
alphamap y z ne (app M N) (fr1 , fr2) with alphamap y z ne M fr1 | alphamap y z ne N fr2
alphamap y z ne (app M N) (fr1 , fr2) | e1 | e2 = cong₂ mapp e1 e2
alphamap y z ne (mask m M d) fr = alphamap y z ne M fr

alphalam : (y z : 𝕏) -> y ≢ z -> (M : 𝕃) -> z ♯ M -> lam y M ≡ lam z (subst M y (var z))
alphalam y z ne M fr with alphamap y z ne M fr | alphaskel y z ne M fr
alphalam y z ne M fr | e1 | e2 = masksubst' (mapskel y M) (mapskel z (fill (mapskel y M) (var z))) e1 e2

-- Lemma 2
substlem : forall {x y N P} -> (M : 𝕃) -> x ≢ y -> x ♯ P -> subst (subst M x N) y P ≡ subst (subst M y P) x (subst N y P)
substlem {x} {y} (var z) ne fr with x =𝕏 z
substlem {.x} {y}{N}{P} (var x) ne fr | inj₁ refl with substvarneq y x P (\e -> ne (sym e))
substlem {.x} {y}{N}{P} (var x) ne fr | inj₁ refl | p rewrite p | substvareq x (subst N y P) = refl
substlem {x}{y}{N}{P} (var z) ne fr | inj₂ p with y =𝕏 z
substlem {x}{.y}{N}{P} (var y) ne fr | inj₂ p | inj₁ refl = sym (substfresh _ _ _ fr)
substlem {x}{y}{N}{P} (var z) ne fr | inj₂ p1 | inj₂ p2 rewrite substvarneq x z (subst N y P) p1 = refl
substlem □ ne fr = refl
substlem {x}{y}{N}{P} (app M M') ne fr with substapp x M M' N | substapp y M M' P
substlem {x} {y} (app M M') ne fr | refl | refl = cong₂ app (substlem M ne fr) (substlem M' ne fr)
substlem {x}{y}{N}{P} (mask m M d) ne fr with substmask x m M N d | substmask y m M P d
substlem (mask m M d) ne fr | refl | refl = masksubst _ _ (substlem M ne fr)

lemma3 : forall {z x N P} -> (M : 𝕃) -> z ≢ x -> map z P ≡ zero -> map z M ≡ map z N -> subst (skel z M) x P ≡ skel z N -> subst M x P ≡ N
lemma3 {z}{x} (var y) ne mz me se with x =𝕏 y
lemma3 {z} (var x) ne mz me se | inj₁ refl with z =𝕏 x
lemma3 (var z) ne mz me se | inj₁ refl | inj₁ refl with ne refl
lemma3 (var z) ne mz me se | inj₁ refl | inj₁ refl | ()
lemma3 {z}{.x}{N}{P} (var x) ne mz me se | inj₁ refl | inj₂ x₁ rewrite substvareq x P | mapzeroskel z N (sym me) = se
lemma3 {z}(var y) ne mz me se | inj₂ x₁ with z =𝕏 y
lemma3 {.z} {x} {var y} (var z) ne mz me se | inj₂ x₂ | inj₁ refl with z =𝕏 y
lemma3 {.z} {x} {var .z} (var z) ne mz me se | inj₂ x₂ | inj₁ refl | inj₁ refl = refl
lemma3 {.z} {x₁} {var y} (var z) ne mz me () | inj₂ x₂ | inj₁ refl | inj₂ x
lemma3 {.z} {x} {□} (var z) ne mz () se | inj₂ x₂ | inj₁ refl
lemma3 {.z} {x} {app N N₁} (var z) ne mz me () | inj₂ x₂ | inj₁ refl
lemma3 {.z} {x} {mask m N x₁} (var z) ne mz me () | inj₂ x₂ | inj₁ refl
lemma3 {z}{x}{N}{P}(var y) ne mz me se | inj₂ x₂ | inj₂ p rewrite substvarneq x y P x₂ | se = mapzeroskel z N (sym me)
lemma3 {z}{x}{N} □ ne mz me se rewrite mapzeroskel z N (sym me) = se
lemma3 {z}{x}{N}{P} (app M M') ne mz me se with substapp x M M' P 
lemma3 {z} {x} {var y} (app M M') ne mz me se | refl with z =𝕏 y
lemma3 {z} {x} {var .z} (app M M') ne mz me () | refl | inj₁ refl
lemma3 {z} {x₁} {var y} (app M M') ne mz me () | refl | inj₂ x
lemma3 {z} {x} {□} (app M M') ne mz me () | refl
lemma3 {z} {x} {app N N'} (app M M') ne mz me se | refl with mappeq0 (map z M) (map z M') (map z N) (map z N') me | appinj se
lemma3 {z} {x} {app N N'} (app M M') ne mz me se | refl | e1 , e2 | e3 , e4 = cong₂ app (lemma3 M ne mz e1 e3) (lemma3 M' ne mz e2 e4)
lemma3 {z} {x} {mask m N x₁} (app M M') ne mz me () | refl
lemma3 {z}{x}{N}{P} (mask m M d) ne mz me se with substmask x m (skel z M) P (skelok d)
lemma3 {z} {x} {var y} (mask m M d) ne mz me se | e with z =𝕏 y
lemma3 {z} {x} {var .z} (mask m M d) ne mz me () | e | inj₁ refl
lemma3 {z} {x₁} {var y} (mask m M d) ne mz me () | e | inj₂ x
lemma3 {z} {x} {□} (mask m M d) ne mz me () | e
lemma3 {z} {x} {app N N₁} (mask m M d) ne mz me () | e
lemma3 {z} {x} {mask n N d'} (mask m M d) ne mz me se | e with maskinj' se
lemma3 {z} {x} {mask .m N d'} (mask m M d) ne mz me se | e | refl , e2 = masksubst _ _ (lemma3 M ne mz me e2)


data _-βη->_ : 𝕃 -> 𝕃 -> Set where
  β : (m : 𝕄)(M N : 𝕃)(d : m ∣ M) -> app (mask m M d) N -βη-> fill d N
  η : (M : 𝕃) -> mask (incl (inr one)) (app M □) (dmapp (zeromask M) ob) -βη-> M
  appl : (M N M' : 𝕃) -> M -βη-> M' -> app M N -βη-> app M' N
  appr : (M N N' : 𝕃) -> N -βη-> N' -> app M N -βη-> app M N'
  ξ : (x : 𝕏)(M N : 𝕃) -> M -βη-> N -> lam x M -βη-> lam x N

-- Check that the parameter form of η holds

ηparam : (x : 𝕏)(M : 𝕃) -> x ♯ M -> lam x (app M (var x)) -βη-> M
ηparam x M fr with freshmap x M fr | mapzeroskel x M (freshmap x M fr) | x =𝕏 x
ηparam x M fr | e1 | e2 | inj₁ refl = substeq (\N -> N -βη-> M) (masksubst' _ _ (substeq (\m -> incl (inr one) ≡ mapp m (incl one)) (sym e1) refl) (substeq (\N -> app M □ ≡ app N □) (sym e2) refl)) (η M)
ηparam x M fr | e1 | e2 | inj₂ p with p refl
ηparam x M fr | e1 | e2 | inj₂ p | ()

-- and β is trivial from the definitions of lam and subst

βparam : (x : 𝕏)(M K : 𝕃) -> app (lam x M) K -βη-> subst M x K
βparam x M K = β _ _ _ _

-- The example that the obvious name-free-ξ doesn't work, because the rhs isn't
-- well formed.

name-free-ξ : Set
name-free-ξ = (m : 𝕄)(M N : 𝕃)(d : m ∣ M) -> M -βη-> N -> Σ (m ∣ N) \d' -> mask m M d -βη-> mask m N d'

name-free-ξ-bad : ¬ name-free-ξ
name-free-ξ-bad nfξ =  bad (proj₁ (nfξ (incl (inr one))
                                   (app (mask (incl one) □ ob) □)
                                   □
                                   (dmapp (dmask zb ob (zl (incl one))) ob)
                                   (β _ _ _ _)))  where
  bad : ¬ (incl (inr one) ∣ □)
  bad ()

-- Here is a version of the ξ rule with a name-free conclusion

mapfill : (x : 𝕏)(m : 𝕄)(M : 𝕃)(d : m ∣ M) -> x ♯ M -> map x (fill d (var x)) ≡ m
mapfill x .zero .(var y) (zv y) fr with x =𝕏 y
mapfill x .zero .(var x) (zv .x) () | inj₁ refl
mapfill x .zero .(var y) (zv  y) fr | inj₂ _ = refl
mapfill x .zero .□ zb fr = refl
mapfill x .(incl one) .□ ob fr with x =𝕏 x
mapfill x .(incl one) .□ ob fr | inj₁ refl = refl
mapfill x .(incl one) .□ ob fr | inj₂ y with y refl
mapfill x .(incl one) .□ ob fr | inj₂ y | ()
mapfill x ._ ._ (dmapp d d') (fr₁ , fr₂) with mapfill x _ _ d fr₁ | mapfill x _ _ d' fr₂
mapfill x ._ ._ (dmapp {m}{n} d d') (fr₁ , fr₂) | e1 | e2 =  substeq (\m' -> mapp m' (map x (fill d' (var x))) ≡ mapp m n) (sym e1) (substeq (\n' -> mapp m n' ≡ mapp m n) (sym e2) refl)
mapfill x m ._ (dmask d d' or) fr = mapfill x m _ d fr

skelfill : (x : 𝕏)(m : 𝕄)(M : 𝕃)(d : m ∣ M) -> x ♯ M -> skel x (fill d (var x)) ≡ M
skelfill x .zero .(var y) (zv y) fr with x =𝕏 y
skelfill x .zero .(var x) (zv .x) () | inj₁ refl
skelfill x .zero .(var y) (zv  y) fr | inj₂ _ = refl
skelfill x .zero .□ zb fr = refl
skelfill x .(incl one) .□ ob fr with x =𝕏 x
skelfill x .(incl one) .□ ob fr | inj₁ refl = refl
skelfill x .(incl one) .□ ob fr | inj₂ y with y refl
skelfill x .(incl one) .□ ob fr | inj₂ y | ()
skelfill x ._ ._ (dmapp d d') (fr₁ , fr₂) with skelfill x _ _ d fr₁ | skelfill x _ _ d' fr₂
skelfill x ._ ._ (dmapp {m}{n}{M}{N} d d') (fr₁ , fr₂) | e1 | e2 = substeq (\M' -> app M' (skel x (fill d' (var x))) ≡ app M N) (sym e1) (substeq (\N' -> app M N' ≡ app M N) (sym e2) refl)
skelfill x m ._ (dmask d d' or) fr = masksubst _ _ (skelfill x _ _ d fr)

name-free-concl-ξ : (x : 𝕏)(m n : 𝕄)(M N : 𝕃) -> 
                    (d : m ∣ M)(d' : n ∣ N) ->
                    x ♯ M -> x ♯ N ->
                    fill d (var x) -βη-> fill d' (var x) ->
                    mask m M d -βη-> mask n N d'
name-free-concl-ξ x m n M N d d' fr1 fr2 be =
    substeq (\M' -> M' -βη-> mask n N d') tm1eq
    (substeq (\N' -> lam x (fill d (var x)) -βη-> N') tm2eq deriv) where
  tm1eq : lam x (fill d (var x)) ≡ mask m M d
  tm1eq = masksubst' _ d (mapfill x m M d fr1) (skelfill x m M d fr1)
  tm2eq : lam x (fill d' (var x)) ≡ mask n N d'
  tm2eq = masksubst' _ d' (mapfill x n N d' fr2) (skelfill x n N d' fr2)
  deriv : lam x (fill d (var x)) -βη-> lam x (fill d' (var x))
  deriv = ξ x (fill d (var x)) (fill d' (var x)) be
