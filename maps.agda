module maps where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

substeq :  forall {k l}{X : Set k}{s t : X} ->
           s == t -> (P : X -> Set l) -> P s -> P t
substeq refl P p = p

symeq : forall {l}{X : Set l} -> {s t : X} -> s == t -> t == s
symeq refl = refl

cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} -> x == y -> f x == f y
cong f refl = refl

cong2 : forall {k l}{X Y : Set k}{Z : Set l}(f : X -> Y -> Z){x x' y y'} -> x == x' -> y == y' -> f x y == f x' y'
cong2 f refl refl = refl

data _===_ {l}{X : Set l}(x : X) : {Y : Set l} -> Y -> Set l where
  refll : x === x


data _×_ {l}(X Y : Set l) : Set l where
  _,_ : X -> Y -> X × Y

pr1 : forall {l}{X Y : Set l} -> X × Y -> X
pr1 (x , y) = x

pr2 : forall {l}{X Y : Set l} -> X × Y -> Y
pr2 (x , y) = y

data _+_ {l}(X Y : Set l) : Set l where
  inl : X -> X + Y
  inr : Y -> X + Y

data Void : Set where

¬ : Set -> Set
¬ X = X -> Void

data Unit : Set where
  〈〉 : Unit

data Sg (X : Set)(Y : X -> Set) : Set where
  _,_ : (x : X) -> Y x -> Sg X Y


postulate 𝕏 : Set
postulate _=𝕏_ : (x y : 𝕏) -> (x == y) + (¬ (x == y))

xrefl : {x : 𝕏} -> x =𝕏 x == inl refl
xrefl {x} with x =𝕏 x
xrefl | inl refl = refl
xrefl | inr e with e refl
xrefl | inr e | ()

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
⊥notunique : ¬ ((m : 𝕄)(n : 𝕄)(p1 : m ⊥ n)(p2 : m ⊥ n) -> p1 == p2)
⊥notunique f with f zero zero (zr zero) (zl zero)
⊥notunique f | ()

⊥notunique' : ¬ ((m : 𝕄)(n : 𝕄)(p1 : m ⊥ n)(p2 : m ⊥ n) -> p1 == p2)
⊥notunique' f with f zero zero (zr zero) (ap (zl zero) (zl zero))
⊥notunique' f | ()

data _⊥_eq : 𝕄 -> 𝕄 -> Set where
  zr : (m n : 𝕄) -> n == zero -> m ⊥ n eq
  zl : (m n : 𝕄) -> m == zero -> m ⊥ n eq
  ap : {m n m' n' m'' n'' : 𝕄} -> m ⊥ n -> m' ⊥ n' -> m'' == mapp m m' -> n'' == mapp n n' -> m'' ⊥ n'' eq

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

mappeq0 : (m n m' n' : 𝕄) -> mapp m n == mapp m' n' -> (m == m') × (n == n')
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

mappeqzero : (m n : 𝕄) -> mapp m n == zero -> (m == zero) × (n == zero)
mappeqzero zero zero refl = refl , refl
mappeqzero zero (incl x) ()
mappeqzero (incl x) zero ()
mappeqzero (incl x) (incl x₁) ()

mappeql : {m n m' n' : 𝕄} -> mapp m n == mapp m' n' -> m == m'
mappeql {m}{n}{m'}{n'} e = pr1 (mappeq0 m n m' n' e)

mappeqr : {m n m' n' : 𝕄} -> mapp m n == mapp m' n' -> n == n'
mappeqr {m}{n}{m'}{n'} e = pr2 (mappeq0 m n m' n' e)

⊥eqsp : (m n m' n' : 𝕄) -> mapp m m' ⊥ mapp n n' eq -> (m ⊥ n) × (m' ⊥ n')
⊥eqsp m n m' n' (zr .(mapp m m') .(mapp n n') e) with mappeqzero n n' e
⊥eqsp m .zero m' .zero (zr .(mapp m m') .(mapp zero zero) e) | refl , refl = zr m , zr m'
⊥eqsp m n m' n' (zl .(mapp m m') .(mapp n n') e) with mappeqzero m m' e
⊥eqsp .zero n .zero n' (zl .(mapp zero zero) .(mapp n n') e) | refl , refl = zl n , zl n'
⊥eqsp m n m' n' (ap {m0}{n0}{m0'}{n0'} o1 o2 e1 e2)  with mappeq0 m m' m0 m0' e1 | mappeq0 n n' n0 n0' e2
⊥eqsp m n m' n' (ap o1 o2 e1 e2) | refl , refl | refl , refl = o1 , o2

⊥left : {m n m' n' : 𝕄} -> mapp m m' ⊥ mapp n n' -> m ⊥ n
⊥left b = pr1 (⊥eqsp _ _ _ _ (⊥eq b))

⊥right : {m n m' n' : 𝕄} -> mapp m m' ⊥ mapp n n' -> m' ⊥ n'
⊥right {m}{n} b = pr2 (⊥eqsp m n _ _ (⊥eq b))

sym⊥ : {m n : 𝕄} -> m ⊥ n -> n ⊥ m
sym⊥ (zr m) = zl m
sym⊥ (zl n) = zr n
sym⊥ (ap b b') = ap (sym⊥ b) (sym⊥ b')

onenotmapp : {X : Set} -> (m n : 𝕄) -> .(incl one == mapp m n) -> X
onenotmapp zero zero ()
onenotmapp zero (incl _) ()
onenotmapp (incl _) zero ()
onenotmapp (incl _) (incl _) ()

one⊥onecases : {X : Set} -> .(incl one ⊥ incl one cases) -> X
one⊥onecases ()

one⊥one : {X : Set} -> .(incl one ⊥ incl one) -> X
one⊥one or = one⊥onecases (⊥cases or)

.one⊥ : {m : 𝕄} -> incl one ⊥ m -> m == zero
one⊥ b with ⊥eq b
one⊥ b | zr .(incl one) m e = e
one⊥ b | zl .(incl one) m ()
one⊥ b | ap {zero} {m' = zero} _ _ () _
one⊥ b | ap {zero} {m' = incl _} _ _ () _
one⊥ b | ap {incl _} {m' = zero} _ _ () _
one⊥ b | ap {incl _} {m' = incl _} _ _ () _

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
  dmappunique : forall {M N m0 m n} -> (y : m0 ∣ app M N) -> m0 == mapp m n -> (d1 : m ∣ M) -> (d2 : n ∣ N) -> dmapp d1 d2 === y
  dmappunique {M}{N}{._}{m'}{n'} (dmapp {m}{n} y y₁) e d1 d2 with mappeql {m}{n}{m'}{n'} e | mappeqr {m}{n}{m'}{n'} e
  dmappunique (dmapp y y₁) e d1 d2 | refl | refl with ∣unique d1 y | ∣unique d2 y₁
  dmappunique (dmapp y y₁) e .y .y₁ | refl | refl | refl | refl = refll

  ∣unique : forall {m M} -> (x y : m ∣ M) -> x == y
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
map x (var .x) | inl refl = incl one
map x (var y)  | inr _ = zero
map x □ = zero
map x (app M N) = mapp (map x M) (map x N)
map x (mask m M _) = map x M

mutual
  skel : 𝕏 -> 𝕃 -> 𝕃
  skel x (var y) with x =𝕏 y
  skel x (var .x) | inl refl = □
  skel x (var y)  | inr _    = var y
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
mapdiv⊥ x (zv .x) | inl refl = zr (incl one)
mapdiv⊥ x (zv y)  | inr _    = zr zero
mapdiv⊥ x zb = zr zero
mapdiv⊥ x ob = zl (incl one)
mapdiv⊥ x (dmapp d d₁) = ap (mapdiv⊥ x d) (mapdiv⊥ x d₁)
mapdiv⊥ x (dmask d d₁ x₁) = mapdiv⊥ x d

mapskel : (x : 𝕏)(M : 𝕃) -> map x M ∣ skel x M
mapskel x (var y) with x =𝕏 y
mapskel x (var .x) | inl refl = ob
mapskel x (var y)  | inr _    = zv _
mapskel x □ = zb
mapskel x (app M N) = dmapp (mapskel x M) (mapskel x N)
mapskel x (mask m M d) = dmask (mapskel x M) (skelok d) (mapdiv⊥ x d)

masksubst : forall {m M M'} -> (d : m ∣ M)(d' : m ∣ M') -> M == M' -> mask m M d == mask m M' d'
masksubst d d' refl with ∣unique d d'
masksubst d .d refl | refl = refl

dmappsubst : forall {m n M N M' N'} -> (d1 : m ∣ M)(d2 : n ∣ N)(d1' : m ∣ M')(d2' : n ∣ N') -> M == M' -> N == N' -> d1 === d1' -> d2 === d2' -> dmapp d1 d2 === dmapp d1' d2'
dmappsubst d1 d2 .d1 .d2 refl refl refll refll = refll

dmasksubst : forall {m n N N'} -> .{or1 or2 : m ⊥ n} -> {d1 : m ∣ N}{d2 : n ∣ N}{d1' : m ∣ N'}{d2' : n ∣ N'} -> N == N' -> dmask d1 d2 or1 === dmask d1' d2' or2
dmasksubst {m}{n}{N}{._}{_}{_}{d1}{d2}{d1'}{d2'} refl with ∣unique d1 d1' | ∣unique d2 d2'
dmasksubst refl | refl | refl = refll

mutual
  mapzeroskel : (x : 𝕏)(M : 𝕃) -> map x M == zero -> skel x M == M
  mapzeroskel x (var y) e with x =𝕏 y
  mapzeroskel x (var .x) () | inl refl
  mapzeroskel x (var y)  e | inr _    = refl
  mapzeroskel x □ e = refl
  mapzeroskel x (app M N) e with mappeqzero (map x M) (map x N) e
  mapzeroskel x (app M N) e | e1 , e2 with mapzeroskel x M e1 | mapzeroskel x N e2
  mapzeroskel x (app M N) e | e1 , e2 | e3 | e4 = cong2 app e3 e4
  mapzeroskel x (mask m M d) e with mapzeroskel x M e
  mapzeroskel x (mask m M d) e | e1 = masksubst _ _ e1
  
  mapzeroskelok : (x : 𝕏)(m : 𝕄)(M : 𝕃)(d : m ∣ M) -> map x M == zero -> skelok {x}{m}{M} d === d
  mapzeroskelok x .zero .(var y) (zv y) e with x =𝕏 y
  mapzeroskelok x .zero .(var x) (zv .x) () | inl refl
  mapzeroskelok x .zero .(var y) (zv y) e | inr x₁ = refll
  mapzeroskelok x .zero .□ zb e = refll
  mapzeroskelok x .(incl one) .□ ob e = refll
  mapzeroskelok x ._ ._ (dmapp {m}{n}{M}{N} d1 d2) e with mappeqzero (map x M) (map x N) e
  mapzeroskelok x ._ ._ (dmapp d1 d2) e | e1 , e2 with mapzeroskelok x _ _ d1 e1 | mapzeroskelok x _ _ d2 e2
  mapzeroskelok x ._ ._ (dmapp d1 d2) e | e1 , e2 | e3 | e4 = dmappsubst (skelok d1) (skelok d2) d1 d2 (mapzeroskel _ _ e1) (mapzeroskel _ _ e2) e3 e4
  mapzeroskelok x m ._ (dmask {.m}{n}{N} d1 d2 or) e with mapzeroskel x N e | mapzeroskelok x _ _ d1 e | mapzeroskelok x _ _ d2 e
  mapzeroskelok x m ._ (dmask d1 d2 or) e | e1 | e2 | e3 = dmasksubst e1

appinj : forall {M N M' N'} -> app M N == app M' N' -> (M == M') × (N == N')
appinj refl = refl , refl

maskinj : forall {m M M' d d'} -> mask m M d == mask m M' d' -> M == M'
maskinj refl = refl

skelmapzero : (x : 𝕏)(M : 𝕃) -> skel x M == M -> map x M == zero
skelmapzero x (var y)  e with x =𝕏 y
skelmapzero x (var .x) () | inl refl
skelmapzero x (var y)   e | inr _    = refl
skelmapzero x □ e = refl
skelmapzero x (app M N) e with appinj e
skelmapzero x (app M N) e | e1 , e2 with skelmapzero x M e1 | skelmapzero x N e2
skelmapzero x (app M N) e | e1 , e2 | e3 | e4 = cong2 mapp e3 e4
skelmapzero x (mask m M d) e = skelmapzero x M (maskinj e)

lam : 𝕏 -> 𝕃 -> 𝕃
lam x M = mask (map x M) (skel x M) (mapskel x M)

subst : 𝕃 -> 𝕏 -> 𝕃 -> 𝕃
subst M x N = fill (mapskel x M) N

-- The comment on 1081 that "if x occurs in M then the corresponding positions
-- in m must be 0" can be expressed by ∣ in the conclusion below:
substdiv : forall {m M} -> (x : 𝕏)(P : 𝕃) -> m ∣ M -> m ∣ subst M x P
substdiv {m}{M} x P d = fillok _ (mapskel x M) (skelok d) (mapdiv⊥ x d)

lamrightinj : forall {x M N} -> lam x M == lam x N -> M == N
lamrightinj e = {!!}

-- Prop 1

substvareq : (x : 𝕏)(P : 𝕃) -> subst (var x) x P == P
substvareq x P with x =𝕏 x
substvareq x P | inl refl = refl
substvareq x P | inr e with e refl
substvareq x P | inr e | ()

substvarneq : (x y : 𝕏)(P : 𝕃) -> ¬ (x == y) -> subst (var y) x P == var y
substvarneq x y n P with x =𝕏 y
substvarneq x y n P | inl e with P e
substvarneq x y n P | inl e | ()
substvarneq x y n P | inr e = refl

substbox : (x : 𝕏)(P : 𝕃) -> subst □ x P == □
substbox x P = refl

substapp : (x : 𝕏)(M N P : 𝕃) -> subst (app M N) x P == app (subst M x P) (subst N x P)
substapp x M N P = refl

substmask : (x : 𝕏)(m : 𝕄)(M P : 𝕃)(d : m ∣ M) -> subst (mask m M d) x P == mask m (subst M x P) (substdiv x P d)
substmask x m M P d = refl

_♯_ : 𝕏 -> 𝕃 -> Set
x ♯ var y with x =𝕏 y
x ♯ var .x | inl refl = Void
x ♯ var y | inr _ = Unit
x ♯ □ = Unit
x ♯ app M N = (x ♯ M) × (x ♯ N)
x ♯ mask m M _ = x ♯ M

mapskelzero : (x : 𝕏)(M : 𝕃) -> map x (skel x M) == zero
mapskelzero x (var y) with x =𝕏 y
mapskelzero x (var .x) | inl refl = refl
-- Do I really need to do this twice?
mapskelzero x (var y) | inr e with x =𝕏 y
mapskelzero x (var y) | inr e | inl e' with e e'
mapskelzero x (var y) | inr e | inl e' | ()
mapskelzero x (var y) | inr e | inr _ = refl
mapskelzero x □ = refl
mapskelzero x (app M N) with mapskelzero x M | mapskelzero x N
mapskelzero x (app M N) | e1 | e2 = cong2 mapp e1 e2
mapskelzero x (mask m M d) = mapskelzero x M

skelidemp : (x : 𝕏)(M : 𝕃) -> skel x (skel x M) == skel x M
skelidemp x M = mapzeroskel x (skel x M) (mapskelzero x M)

dmappinv : (m : 𝕄)(M N : 𝕃) -> (d : m ∣ app M N) -> Sg 𝕄 \m1 -> Sg 𝕄 \m2 -> Sg (m1 ∣ M) \d1 -> Sg (m2 ∣ N) \d2 -> (mapp m1 m2 == m) × (d === dmapp {m1}{m2}{M}{N} d1 d2)
dmappinv ._ M N (dmapp {m}{n} d1 d2) = m , (n , (d1 , (d2 , (refl , refll))))

dmappzero : (M N : 𝕃) -> (d : zero ∣ app M N) -> Sg (zero ∣ M) \d1 -> Sg (zero ∣ N) \d2 -> d === dmapp {zero}{zero}{M}{N} d1 d2
dmappzero M N d with dmappinv zero M N d
dmappzero M N d | m1 , (m2 , (d1 , (d2 , (e1 , e2)))) with mappeqzero m1 m2 e1
dmappzero M N d | .zero , (.zero , (d1 , (d2 , (e1 , e2)))) | refl , refl = d1 , (d2 , e2)

mutual
  fillzero : (M P : 𝕃)(d : zero ∣ M) -> fill {zero} d P == M
  fillzero (var x) P (zv .x) = refl
  fillzero □ P zb = refl
  fillzero (app M N) P d with dmappzero M N d
  fillzero (app M N) P .(dmapp d1 d2) | d1 , (d2 , refll) = cong2 app (fillzero M P d1) (fillzero N P d2)
  fillzero (mask m M x) P (dmask d .x or) with fillzero M P d
  fillzero (mask m M d1) P (dmask d .d1 or) | e = masksubst _ _ e

  fillokzero : forall {M P m} -> .(or : zero ⊥ m) -> (d1 : zero ∣ M) -> (d2 : m ∣ M) -> fill d1 P == M -> fillok {m}{M}{P} zero d1 d2 or === d2
  fillokzero {var .x} or (zv x) e x₁ = refll
  fillokzero {□} or zb e x = refll
  fillokzero {app M N} or d e x with dmappzero M N d
  fillokzero {app M N}{P} or .(dmapp d1 d2) (dmapp d3 d4) x₃ | d1 , (d2 , refll) = dmappsubst _ _ _ _ (fillzero M P d1) (fillzero N P d2) (fillokzero _ d1 d3 (fillzero M P d1)) (fillokzero _ d2 d4 (fillzero N P d2))
  fillokzero {mask n N .d'}{P} or (dmask d d' x) (dmask e .d' x₁) x₂ = dmasksubst (fillzero N P d)
  

fillzeroeq : (m : 𝕄)(M M' P : 𝕃)(d : m ∣ M') -> m == zero -> M' == M -> fill d P == M
fillzeroeq .zero M .M P d refl refl = fillzero M P d

diveq : forall {x M} -> map x M == zero -> map x M ∣ M
diveq {x}{M} e = substeq (symeq e) (\m -> m ∣ M) (zeromask _)

substskel : (x : 𝕏)(M P : 𝕃) -> subst (skel x M) x P == skel x M
substskel x M P with mapskelzero x M
substskel x M P | e =  fillzeroeq _ _ _ P (mapskel x (skel x M)) e (skelidemp x M) 

substlameq : (x : 𝕏)(M P : 𝕃) -> subst (lam x M) x P == lam x M
substlameq x M P with substskel x M P
substlameq x M P | e = masksubst _ _ e

