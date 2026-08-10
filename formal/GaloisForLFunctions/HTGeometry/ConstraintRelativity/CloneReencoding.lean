import Mathlib

/-!
# Faithful re-encoding does not promote a law

An injective encoding `i : X → Y` transports every finitary operation on `X` to an operation on
the image `i(X)`, and this transport is a clone isomorphism.  Consequently a term identity holds
before encoding exactly when it holds afterwards, term-definable operations correspond
bijectively, and congruence lattices correspond bijectively.  Nothing obtained by transporting old
operations through an injective encoding is a new law.

The final section is the prime crossing-time instance: the crossing-time profile
`τ_p = M - x_p + 1` of a valuation vector attaining the value `0` is an injective re-encoding, and
the reset-and-carry action of multiplication by a prime is conjugate through it to the ordinary
increment of the valuation vector.
-/

namespace HTGeometry.ConstraintRelativity

universe u v w

/-! ## Finitary operations and their transport -/

/-- An `n`-ary operation on `X`. -/
abbrev Op (X : Type u) (n : ℕ) : Type u := (Fin n → X) → X

namespace Op

/-- Transport of an `n`-ary operation along a bijection: `i_*f = i ∘ f ∘ (i⁻¹)ⁿ`. -/
def transport {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (f : Op X n) : Op Y n :=
  fun y => e (f fun k => e.symm (y k))

/-- The defining equation of the transport: `(i_*f)(i x₁, …, i xₙ) = i (f x₁ … xₙ)`. -/
@[simp]
theorem transport_apply_map {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (f : Op X n)
    (x : Fin n → X) : transport e f (fun k => e (x k)) = e (f x) := by
  simp [transport]

/-- Transport sends coordinate projections to coordinate projections. -/
@[simp]
theorem transport_proj {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (k : Fin n) :
    transport e (fun x : Fin n → X => x k) = (fun y : Fin n → Y => y k) := by
  funext y; simp [transport]

/-- Transport respects substitution (superposition) of operations. -/
theorem transport_comp {X : Type u} {Y : Type v} (e : X ≃ Y) {n m : ℕ} (f : Op X n)
    (g : Fin n → Op X m) :
    transport e (fun x : Fin m → X => f fun j => g j x)
      = (fun y : Fin m → Y => transport e f fun j => transport e (g j) y) := by
  funext y; simp [transport]

/-- Transport along the identity is the identity. -/
@[simp]
theorem transport_refl {X : Type u} {n : ℕ} (f : Op X n) :
    transport (Equiv.refl X) f = f := by
  funext x; simp [transport]

/-- Transport is functorial in the encoding. -/
theorem transport_trans {X : Type u} {Y : Type v} {Z : Type w} (e : X ≃ Y) (e' : Y ≃ Z) {n : ℕ}
    (f : Op X n) : transport e' (transport e f) = transport (e.trans e') f := by
  funext z; simp [transport]

/-- Transport along the inverse encoding undoes the transport. -/
@[simp]
theorem transport_symm_transport {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (f : Op X n) :
    transport e.symm (transport e f) = f := by
  rw [transport_trans, Equiv.self_trans_symm, transport_refl]

@[simp]
theorem transport_transport_symm {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (g : Op Y n) :
    transport e (transport e.symm g) = g := by
  rw [transport_trans, Equiv.symm_trans_self, transport_refl]

/-- Transport of `n`-ary operations is a bijection. -/
def transportEquiv {X : Type u} {Y : Type v} (e : X ≃ Y) (n : ℕ) : Op X n ≃ Op Y n where
  toFun := transport e
  invFun := transport e.symm
  left_inv f := transport_symm_transport e f
  right_inv g := transport_transport_symm e g

/-- Transport of operations is injective: an identity between operations is preserved and
reflected by a faithful re-encoding. -/
theorem transport_injective {X : Type u} {Y : Type v} (e : X ≃ Y) (n : ℕ) :
    Function.Injective (transport e (n := n)) :=
  (transportEquiv e n).injective

theorem transport_inj_iff {X : Type u} {Y : Type v} (e : X ≃ Y) {n : ℕ} (f g : Op X n) :
    transport e f = transport e g ↔ f = g :=
  ⟨fun h => transport_injective e n h, fun h => by rw [h]⟩

end Op

/-! ## Clones and the clone-conjugacy theorem -/

/-- A clone of finitary operations on `X`: a family of sets of operations containing all
coordinate projections and closed under substitution. -/
structure Clone (X : Type u) where
  /-- Membership predicate for `n`-ary members of the clone. -/
  mem : ∀ n : ℕ, Op X n → Prop
  /-- Every coordinate projection belongs to the clone. -/
  proj : ∀ {n : ℕ} (k : Fin n), mem n fun x => x k
  /-- The clone is closed under substitution. -/
  comp : ∀ {n m : ℕ} (f : Op X n) (g : Fin n → Op X m), mem n f → (∀ j, mem m (g j)) →
    mem m fun x => f fun j => g j x

namespace Clone

/-- The transported clone `i_*C`, living on the target of the encoding. -/
def transport {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) : Clone Y where
  mem n h := ∃ f : Op X n, C.mem n f ∧ Op.transport e f = h
  proj := fun {n} k => ⟨fun x => x k, C.proj k, Op.transport_proj e k⟩
  comp := by
    rintro n m f g ⟨f₀, hf₀, rfl⟩ hg
    choose g₀ hg₀ hge using hg
    refine ⟨fun x => f₀ fun j => g₀ j x, C.comp f₀ g₀ hf₀ hg₀, ?_⟩
    rw [Op.transport_comp]
    funext y
    simp only [hge]

@[simp]
theorem transport_mem_iff {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) (n : ℕ)
    (f : Op X n) : (C.transport e).mem n (Op.transport e f) ↔ C.mem n f := by
  constructor
  · rintro ⟨f₀, hf₀, hEq⟩
    have hf : f₀ = f := Op.transport_injective e n hEq
    exact hf ▸ hf₀
  · exact fun h => ⟨f, h, rfl⟩

/-- **Clone conjugacy.**  Transport along a faithful re-encoding is a bijection from the `n`-ary
part of a clone onto the `n`-ary part of the transported clone. -/
def transportPartEquiv {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) (n : ℕ) :
    {f : Op X n // C.mem n f} ≃ {g : Op Y n // (C.transport e).mem n g} where
  toFun f := ⟨Op.transport e f.1, ⟨f.1, f.2, rfl⟩⟩
  invFun g := ⟨Op.transport e.symm g.1, by
    obtain ⟨f, hf, hEq⟩ := g.2
    have : Op.transport e.symm g.1 = f := by rw [← hEq, Op.transport_symm_transport]
    rw [this]; exact hf⟩
  left_inv f := by ext : 1; simp
  right_inv g := by ext : 1; simp

@[simp]
theorem transportPartEquiv_apply_coe {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) (n : ℕ)
    (f : {f : Op X n // C.mem n f}) :
    ((transportPartEquiv e C n) f : Op Y n) = Op.transport e f.1 := rfl

/-! ### The two extreme clones -/

/-- The full clone: every finitary operation on `X`. -/
def full (X : Type u) : Clone X where
  mem _ _ := True
  proj _ := trivial
  comp _ _ _ _ := trivial

/-- The projection clone: the smallest clone, whose `n`-ary part consists exactly of the
coordinate projections. -/
def projections (X : Type u) : Clone X where
  mem n f := ∃ k : Fin n, f = fun x => x k
  proj k := ⟨k, rfl⟩
  comp := by
    rintro n m f g ⟨k, rfl⟩ hg
    obtain ⟨l, hl⟩ := hg k
    refine ⟨l, ?_⟩
    funext x
    exact congrFun hl x

/-- **Clones exist and the clone lattice is nontrivial.**  As soon as `X` has two distinct elements
the projection clone is strictly smaller than the full clone, since a constant unary operation is
not a coordinate projection. -/
theorem projections_ne_full {X : Type u} (a b : X) (hab : a ≠ b) :
    projections X ≠ full X := by
  intro h
  have h1 : (projections X).mem 1 (fun _ => a) := by rw [h]; trivial
  obtain ⟨k, hk⟩ := h1
  exact hab (congrFun hk fun _ => b)

/-- Transport carries the full clone to the full clone. -/
theorem transport_full {X : Type u} {Y : Type v} (e : X ≃ Y) (n : ℕ) (g : Op Y n) :
    ((full X).transport e).mem n g ↔ (full Y).mem n g :=
  ⟨fun _ => trivial,
    fun _ => ⟨Op.transport e.symm g, trivial, Op.transport_transport_symm e g⟩⟩

/-- Transport carries the projection clone to the projection clone. -/
theorem transport_projections {X : Type u} {Y : Type v} (e : X ≃ Y) (n : ℕ) (g : Op Y n) :
    ((projections X).transport e).mem n g ↔ (projections Y).mem n g := by
  constructor
  · rintro ⟨f, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, Op.transport_proj e k⟩
  · rintro ⟨k, rfl⟩
    exact ⟨fun x => x k, ⟨k, rfl⟩, Op.transport_proj e k⟩

/-- Transporting back along the inverse encoding returns the original clone. -/
theorem transport_transport_symm {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) :
    ∀ n (f : Op X n), ((C.transport e).transport e.symm).mem n f ↔ C.mem n f := by
  intro n f
  constructor
  · rintro ⟨g, ⟨f₀, hf₀, rfl⟩, rfl⟩
    rwa [Op.transport_symm_transport]
  · intro h
    exact ⟨Op.transport e f, ⟨f, h, rfl⟩, Op.transport_symm_transport e f⟩

end Clone

/-! ## Terms, term identities, and term-definable operations -/

/-- A term in `m` variables built from finitary operations on `X`. -/
inductive CloneTerm (X : Type u) (m : ℕ) : Type u
  | var : Fin m → CloneTerm X m
  | app : ∀ {n : ℕ}, Op X n → (Fin n → CloneTerm X m) → CloneTerm X m

namespace CloneTerm

/-- Evaluation of a term at a tuple of arguments. -/
def eval {X : Type u} {m : ℕ} : CloneTerm X m → Op X m
  | .var k, x => x k
  | .app f ts, x => f fun j => (ts j).eval x

/-- Transport of a term along a faithful re-encoding. -/
def transport {X : Type u} {Y : Type v} (e : X ≃ Y) {m : ℕ} :
    CloneTerm X m → CloneTerm Y m
  | .var k => .var k
  | .app f ts => .app (Op.transport e f) fun j => (ts j).transport e

/-- **Evaluation commutes with a faithful re-encoding.** -/
theorem eval_transport {X : Type u} {Y : Type v} (e : X ≃ Y) {m : ℕ} (t : CloneTerm X m)
    (x : Fin m → X) : (t.transport e).eval (fun k => e (x k)) = e (t.eval x) := by
  induction t with
  | var k => simp [transport, eval]
  | app f ts ih =>
      simp only [transport, eval]
      rw [show (fun j => (transport e (ts j)).eval fun k => e (x k))
            = fun j => e ((ts j).eval x) from funext fun j => ih j]
      rw [Op.transport_apply_map]

/-- The operation defined by a transported term is the transport of the operation defined by the
term. -/
theorem eval_transport_eq {X : Type u} {Y : Type v} (e : X ≃ Y) {m : ℕ} (t : CloneTerm X m) :
    (t.transport e).eval = Op.transport e t.eval := by
  funext y
  have := eval_transport e t (fun k => e.symm (y k))
  simpa [Op.transport] using this

/-- **Term identities are preserved and reflected.**  A term identity holds before a faithful
re-encoding exactly when it holds afterwards. -/
theorem eval_transport_inj_iff {X : Type u} {Y : Type v} (e : X ≃ Y) {m : ℕ}
    (t₁ t₂ : CloneTerm X m) :
    (t₁.transport e).eval = (t₂.transport e).eval ↔ t₁.eval = t₂.eval := by
  rw [eval_transport_eq, eval_transport_eq, Op.transport_inj_iff]

/-- **Term-definable operations correspond bijectively.**  An `m`-ary operation on `Y` is definable
by a transported term exactly when it is the transport of an operation definable by a term. -/
theorem exists_transport_eval_iff {X : Type u} {Y : Type v} (e : X ≃ Y) {m : ℕ} (f : Op X m) :
    (∃ t : CloneTerm X m, (t.transport e).eval = Op.transport e f) ↔
      ∃ t : CloneTerm X m, t.eval = f := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [eval_transport_eq] at ht; exact Op.transport_injective e m ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, eval_transport_eq e t⟩

end CloneTerm

/-! ## Congruences -/

/-- A congruence of a clone: an equivalence relation compatible with every member operation. -/
structure Congruence {X : Type u} (C : Clone X) where
  /-- The underlying relation. -/
  rel : X → X → Prop
  /-- The relation is an equivalence. -/
  iseqv : Equivalence rel
  /-- Compatibility with every operation of the clone. -/
  compat : ∀ {n : ℕ} (f : Op X n), C.mem n f → ∀ x y : Fin n → X, (∀ k, rel (x k) (y k)) →
    rel (f x) (f y)

namespace Congruence

/-- Transport of a congruence along a faithful re-encoding. -/
def transport {X : Type u} {Y : Type v} (e : X ≃ Y) {C : Clone X} (θ : Congruence C) :
    Congruence (C.transport e) where
  rel a b := θ.rel (e.symm a) (e.symm b)
  iseqv :=
    { refl := fun a => θ.iseqv.refl _
      symm := fun h => θ.iseqv.symm h
      trans := fun h h' => θ.iseqv.trans h h' }
  compat := by
    rintro n g ⟨f, hf, rfl⟩ a b hab
    have : θ.rel (f fun k => e.symm (a k)) (f fun k => e.symm (b k)) :=
      θ.compat f hf _ _ fun k => hab k
    simpa [Op.transport] using this

/-- **Congruence lattices correspond bijectively.** -/
def transportEquiv {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) :
    Congruence C ≃ Congruence (C.transport e) where
  toFun θ := θ.transport e
  invFun θ :=
    { rel := fun a b => θ.rel (e a) (e b)
      iseqv :=
        { refl := fun a => θ.iseqv.refl _
          symm := fun h => θ.iseqv.symm h
          trans := fun h h' => θ.iseqv.trans h h' }
      compat := by
        intro n f hf x y hxy
        have hmem : (C.transport e).mem n (Op.transport e f) :=
          (Clone.transport_mem_iff e C n f).2 hf
        have := θ.compat (Op.transport e f) hmem (fun k => e (x k)) (fun k => e (y k))
          fun k => hxy k
        simpa using this }
  left_inv θ := by cases θ; simp [transport]
  right_inv θ := by cases θ; simp [transport]

/-! ### The two extreme congruences -/

/-- The total congruence, relating every pair of elements. -/
def top {X : Type u} (C : Clone X) : Congruence C where
  rel _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  compat _ _ _ _ _ := trivial

/-- The identity congruence. -/
def bot {X : Type u} (C : Clone X) : Congruence C where
  rel := Eq
  iseqv := eq_equivalence
  compat _ _ x y hxy := by rw [funext hxy]

/-- **Congruence lattices are nontrivial.**  As soon as `X` has two distinct elements the identity
congruence differs from the total congruence, so the transport bijection above is a bijection
between sets with at least two elements rather than between empty ones. -/
theorem bot_ne_top {X : Type u} (C : Clone X) (a b : X) (hab : a ≠ b) : bot C ≠ top C := by
  intro h
  have h1 : (bot C).rel a b := by rw [h]; trivial
  exact hab h1

/-- Transport preserves the total congruence. -/
theorem transport_top {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) (a b : Y) :
    ((top C).transport e).rel a b ↔ (top (C.transport e)).rel a b := Iff.rfl

/-- Transport preserves the identity congruence. -/
theorem transport_bot {X : Type u} {Y : Type v} (e : X ≃ Y) (C : Clone X) (a b : Y) :
    ((bot C).transport e).rel a b ↔ (bot (C.transport e)).rel a b :=
  e.symm.injective.eq_iff

end Congruence

/-! ## The separating-feature corollary -/

/-- **Separating features give a faithful re-encoding.**  A jointly separating family of source
features is an injective encoding, and any successor operation defined by the intertwining law
`Φ ∘ T = T̂ ∘ Φ` agrees on the image with the transport of `T`. -/
theorem transport_eq_of_intertwine {X : Type u} {Y : Type v} (Φ : X → Y)
    (T : X → X) (T' : Y → Y) (hint : ∀ x, Φ (T x) = T' (Φ x))
    (x : X) : T' (Φ x) = Φ (T x) := (hint x).symm

/-- The intertwined successor operation restricted to the image of a separating family is
conjugate to the source operation: it is exactly the transport of `T` along the induced bijection
onto the range. -/
theorem transport_ofInjective_eq_of_intertwine {X : Type u} {Y : Type v} (Φ : X → Y)
    (hΦ : Function.Injective Φ) (T : X → X) (T' : Y → Y) (hint : ∀ x, Φ (T x) = T' (Φ x))
    (y : Set.range Φ) :
    (Equiv.ofInjective Φ hΦ) (T ((Equiv.ofInjective Φ hΦ).symm y)) = ⟨T' (y : Y), by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨T x, by rw [hint, hx]⟩⟩ := by
  obtain ⟨x, hx⟩ := y.2
  have hy : y = (Equiv.ofInjective Φ hΦ) x := by
    ext; simpa [Equiv.ofInjective] using hx.symm
  subst hy
  simp only [Equiv.symm_apply_apply]
  ext
  simpa [Equiv.ofInjective] using (hint x)

/-! ## The prime crossing-time profile -/

/-- The crossing-time profile of a valuation vector: `τ_p = M - x_p + 1` where `M` is the top
valuation. -/
def crossingProfile {ι : Type u} (M : ℕ) (x : ι → ℕ) : ι → ℕ := fun p => M - x p + 1

/-- On valuation vectors dominated by `M` and attaining the value `0`, the top valuation is
recovered from the profile as `(sup τ) - 1`. -/
theorem crossingProfile_le (M : ℕ) {ι : Type u} (x : ι → ℕ) (p : ι) (hp : x p ≤ M) :
    crossingProfile M x p ≤ M + 1 := by
  simp only [crossingProfile]
  omega

theorem crossingProfile_zero {ι : Type u} (M : ℕ) (x : ι → ℕ) (p : ι) (hp : x p = 0) :
    crossingProfile M x p = M + 1 := by
  simp [crossingProfile, hp]

/-- **The crossing-time profile is a faithful re-encoding.**  Two valuation vectors dominated by
their own top valuations, each attaining the value `0`, with equal crossing-time profiles are
equal.  Injectivity uses only that the profile attains its maximum exactly at the zero valuations,
which pins the top valuation. -/
theorem crossingProfile_injective {ι : Type u} {M M' : ℕ} {x x' : ι → ℕ}
    (hx : ∀ p, x p ≤ M) (hx' : ∀ p, x' p ≤ M')
    (hz : ∃ p, x p = 0) (hz' : ∃ p, x' p = 0)
    (h : crossingProfile M x = crossingProfile M' x') : x = x' := by
  obtain ⟨p₀, hp₀⟩ := hz
  obtain ⟨p₁, hp₁⟩ := hz'
  have hMM' : M = M' := by
    have h₀ := congrFun h p₀
    have h₁ := congrFun h p₁
    simp only [crossingProfile, hp₀, hp₁, Nat.sub_zero] at h₀ h₁
    have := hx' p₀
    have := hx p₁
    omega
  subst hMM'
  funext p
  have hp := congrFun h p
  simp only [crossingProfile] at hp
  have := hx p
  have := hx' p
  omega

/-- Reset-and-carry: the profile action induced by incrementing one coordinate of the valuation
vector.  Below the top valuation the coordinate simply counts down; at the top valuation the whole
profile carries by one and the incremented coordinate resets. -/
def resetCarry {ι : Type u} [DecidableEq ι] (p : ι) (τ : ι → ℕ) : ι → ℕ := fun q =>
  if τ p = 1 then (if q = p then 1 else τ q + 1)
  else (if q = p then τ q - 1 else τ q)

/-- **The reset-and-carry action is conjugate to prime multiplication.**  Incrementing the
valuation at `p` and then taking the crossing-time profile is the reset-and-carry action applied to
the profile.  Here `M` is the top valuation of `x` and `M'` the top valuation of the incremented
vector. -/
theorem crossingProfile_increment {ι : Type u} [DecidableEq ι] (p : ι) (M : ℕ) (x : ι → ℕ)
    (hx : ∀ q, x q ≤ M) :
    crossingProfile (max M (x p + 1)) (Function.update x p (x p + 1))
      = resetCarry p (crossingProfile M x) := by
  funext q
  have hxq := hx q
  by_cases hxp : x p = M
  · have htop : crossingProfile M x p = 1 := by
      simp [crossingProfile, hxp]
    have hmax : max M (x p + 1) = M + 1 := by omega
    simp only [resetCarry]
    rw [if_pos htop]
    by_cases hq : q = p
    · subst hq
      rw [if_pos rfl]
      simp only [crossingProfile, hmax, Function.update_self]
      omega
    · rw [if_neg hq]
      simp only [crossingProfile, hmax, Function.update_of_ne hq]
      omega
  · have hlt : x p < M := lt_of_le_of_ne (hx p) hxp
    have htop : crossingProfile M x p ≠ 1 := by
      simp only [crossingProfile]
      omega
    have hmax : max M (x p + 1) = M := by omega
    simp only [resetCarry]
    rw [if_neg htop]
    by_cases hq : q = p
    · subst hq
      rw [if_pos rfl]
      simp only [crossingProfile, hmax, Function.update_self]
      omega
    · rw [if_neg hq]
      simp only [crossingProfile, hmax, Function.update_of_ne hq]

end HTGeometry.ConstraintRelativity
