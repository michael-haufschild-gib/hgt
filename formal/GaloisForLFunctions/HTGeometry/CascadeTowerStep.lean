import GaloisForLFunctions.HTGeometry.CascadeLaurentLevelJacobian
import GaloisForLFunctions.HTGeometry.RationalFunctionFieldRootExtension
import GaloisForLFunctions.HTGeometry.FirstOrderRelationSpecialization
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# One step of the Laurent tower of a first-order cascade

A *model* of a differential field `B` (over `ℂ`, with a rational clock `ℂ(z) → B`) at depth `j` is
an algebraically closed field `K` with a time derivation `δ_K`, `j` coordinate derivations killing
the clock, and a differential embedding `B → K`.

Let `B' = B(X, v)` be the next cascade field: `X` transcendental over `B`, `v` a root of the
layer relation `P(X_s, X, W)` (irreducible over `B(V)`), `δX = G v` with `G = δX_s`.  Given a model
of `B` and a nonzero root `σ` of the top symbol `Q(ι X_s, ·)`, the Newton--Puiseux branch of `P`
with lead `σ` gives an embedding `ι' : B' → K((t))` with `X ↦ t^(-N)` and `v ↦ ρ`, `ρ` of degree
`-N` and lead `σ`.  With `A = t^N ι'(G v)` (order zero, constant term `σ ι(G)`), `ι'` is
differential for `δ = δ_K - (A/N) t d/dt`, because both sides agree on `B` and at `X`, and hence on
the separable algebraic `v`.  Passing to an algebraic closure gives a model of `B'` at depth
`j + 1`.
-/

open Polynomial HahnSeries IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentDerivation

attribute [local instance 2000] Algebra.toModule

/-- A model of a differential field `B` with clock `rat` at depth `j`. -/
structure CascadeModel (B : Type) [Field B] [Algebra ℂ B] (δB : Derivation ℂ B B)
    (rat : RatFunc ℂ →+* B) (j : ℕ) where
  /-- The model field. -/
  K : Type
  [field : Field K]
  [isAlgClosed : IsAlgClosed K]
  [charZero : CharZero K]
  [algebra : Algebra ℂ K]
  /-- The time derivation of the model. -/
  δK : Derivation ℂ K K
  /-- The coordinate derivations of the model. -/
  pK : Fin j → Derivation ℂ K K
  /-- The embedding of `B`. -/
  ι : B →+* K
  map_deriv : ∀ x, ι (δB x) = δK (ι x)
  map_complex : ∀ c : ℂ, ι (algebraMap ℂ B c) = algebraMap ℂ K c
  coord_rat : ∀ i r, pK i (ι (rat r)) = 0

attribute [instance] CascadeModel.field CascadeModel.isAlgClosed CascadeModel.charZero
  CascadeModel.algebra

variable {B : Type} [Field B] [Algebra ℂ B] {δB : Derivation ℂ B B} {rat : RatFunc ℂ →+* B}
  {j : ℕ}

/-- A Wiman lead of a layer relation `(S, A, d)` at state `Xs` with velocity `G = δX_s` in a model:
a nonzero root `σ` of the top symbol at the image of `Xs`, together with the two Jacobian
nonvanishings that the next level consumes. -/
structure CascadeModel.WimanLead (M : CascadeModel B δB rat j) (S : Finset (ℕ × ℕ))
    (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (Xs G : B) where
  σ : M.K
  isRoot : (topSymbolAt S A d (M.ι Xs)).IsRoot σ
  topSymbol_ne : topSymbolAt S A d (M.ι Xs) ≠ 0
  lead_ne : σ * M.ι G ≠ 0
  jac_top : (Matrix.of fun r i : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)])
    (σ * M.ι G))).det ≠ 0
  jac_step : ∀ lam : ℂ, lam ≠ 0 → (Matrix.of fun r i : Fin j => M.pK i
    (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.δK (σ * M.ι G) / (σ * M.ι G) +
      algebraMap ℂ M.K lam * (σ * M.ι G)))).det ≠ 0

/-- Evaluation of a first-order relation, split at the derivative variable, at `(X, v)`. -/
theorem eval₂_relPolyVia {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {F E : Type*}
    [Field F] [CommRing E] (φ : RatFunc ℂ →+* F) (e : F →+* E) (X v : E) :
    (relPolyVia S A φ).eval₂ (eval₂RingHom e X) v =
      ∑ i ∈ S, e (φ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (A i))) * X ^ i.1 * v ^ i.2 := by
  rw [relPolyVia, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval₂_mul, eval₂_C, eval₂_X_pow, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow]

/-- A ring map compatible with the complex structures commutes with complex polynomial
evaluation. -/
theorem ringHom_aeval_of_complex {F E : Type*} [CommRing F] [CommRing E] [Algebra ℂ F]
    [Algebra ℂ E] (e : F →+* E) (he : ∀ c : ℂ, e (algebraMap ℂ F c) = algebraMap ℂ E c)
    (x : F) (p : Polynomial ℂ) : e (aeval x p) = aeval (e x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact RingHom.ext he

/-- The output of one tower step: an embedding of the next cascade field into `K((t))` sending
the new state to `t^(-N)`, `N = R m`, differential for the layer time derivation with logarithmic
velocity `A`, whose constant term is `A₀`. -/
structure CascadeModel.StepData (M : CascadeModel B δB rat j) {B' : Type} [Field B']
    [Algebra ℂ B'] (δB' : Derivation ℂ B' B') (incl : B →ₐ[ℂ] B') (G : B) (X v : B')
    (A₀ : M.K) (m : ℕ) where
  R : ℕ
  R_ne : R ≠ 0
  Aser : LaurentSeries M.K
  ι' : B' →+* LaurentSeries M.K
  map_incl : ∀ x, ι' (incl x) = HahnSeries.C (M.ι x)
  map_X : ι' X = single (-((R * m : ℕ) : ℤ)) 1
  lead : HasLead Aser 0 A₀
  map_Gv : ι' (incl G * v) = Aser * single (-((R * m : ℕ) : ℤ)) 1
  map_deriv : ∀ x, ι' (δB' x) = levelTime M.δK (R * m) Aser (ι' x)
  map_complex : ∀ c : ℂ, ι' (algebraMap ℂ B' c) = algebraMap ℂ (LaurentSeries M.K) c

/-- **One step of the tower.**  A Wiman lead of the layer relation at a model of `B` yields an
embedding of `B' = B(X, v)` into `K((t))` with `X ↦ t^(-R m)`, differential for the layer time
derivation whose logarithmic velocity `A` has constant term `σ ι(G)`. -/
theorem CascadeModel.exists_step {B' : Type} [Field B'] [Algebra ℂ B']
    {δB' : Derivation ℂ B' B'} (incl : B →ₐ[ℂ] B') (hincl : ∀ x, δB' (incl x) = incl (δB x))
    (M : CascadeModel B δB rat j) {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ i ∈ S, i.1 + i.2 ≤ d) (hA : ∀ i ∈ S, A i ≠ 0) {Xs G : B} {X v : B'}
    (hX' : δB' X = incl G * v) (φ : RatFunc ℂ →+* B)
    (hφ : ∀ p, φ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = aeval Xs p)
    (hirr : Irreducible ((relPolyVia S A φ).map (algebraMap (Polynomial B) (RatFunc B))))
    (hXtr : letI : Algebra B B' := incl.toRingHom.toAlgebra; Transcendental B X)
    (htop : adjoin ℂ (Set.range incl ∪ {X, v}) = ⊤)
    (hrel : ∑ i ∈ S, incl (aeval Xs (A i)) * X ^ i.1 * v ^ i.2 = 0)
    (w : M.WimanLead S A d Xs G) (m : ℕ) (hm : m ≠ 0) :
    Nonempty (M.StepData δB' incl G X v (w.σ * M.ι G) m) := by
  classical
  haveI : CharZero B := charZero_of_injective_algebraMap (algebraMap ℂ B).injective
  letI algBB' : Algebra B B' := incl.toRingHom.toAlgebra
  have halg : ∀ x, algebraMap B B' x = incl x := fun _ => rfl
  haveI : IsScalarTower ℂ B B' := IsScalarTower.of_algebraMap_eq fun c => (incl.commutes c).symm
  have htop' : adjoin B {X, v} = ⊤ := by
    rw [eq_top_iff]
    have hle : adjoin ℂ (Set.range incl ∪ {X, v}) ≤ (adjoin B {X, v}).restrictScalars ℂ := by
      rw [adjoin_le_iff]
      rintro y (⟨x, rfl⟩ | hy)
      · exact (adjoin B {X, v}).algebraMap_mem x
      · exact subset_adjoin B {X, v} hy
    rw [htop] at hle
    intro y _
    exact hle (show y ∈ (⊤ : IntermediateField ℂ B') from trivial)
  obtain ⟨R, hR, z, hz0, hroot⟩ := exists_relation_laurent_branch (K := M.K) S A d hdeg hA
    (M.ι Xs) w.σ w.topSymbol_ne w.isRoot
  set N : ℕ := R * m with hNdef
  have hN : N ≠ 0 := Nat.mul_ne_zero hR hm
  set τ : LaurentSeries M.K := single (-(N : ℤ)) 1 with hτdef
  set ρ : LaurentSeries M.K :=
    laurentExpand m hm (single (-(R : ℤ)) 1 * ofPowerSeries ℤ M.K z) with hρdef
  have hτ_eq : laurentExpand m hm (single (-(R : ℤ)) (1 : M.K)) = τ := by
    rw [laurentExpand_single, hτdef, hNdef,
      show (m : ℤ) * -(R : ℤ) = -((R * m : ℕ) : ℤ) by push_cast; ring]
  have hsum : ∑ i ∈ S, HahnSeries.C (aeval (M.ι Xs) (A i)) * τ ^ i.1 * ρ ^ i.2 = 0 := by
    have h0 := hroot
    rw [eval₂_firstOrderMvPoly_laurent] at h0
    have h1 := congrArg (laurentExpand m hm) h0
    rw [map_sum, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, laurentExpand_C, hτ_eq]
  let ι₀ : B →+* LaurentSeries M.K := (HahnSeries.C : M.K →+* LaurentSeries M.K).comp M.ι
  have hι₀ : ∀ x, ι₀ x = HahnSeries.C (M.ι x) := fun _ => rfl
  have hτinj : Function.Injective (eval₂RingHom ι₀ τ) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hmap : p.map M.ι ≠ 0 := Polynomial.map_ne_zero hp0
    apply polynomial_eval₂_laurent_single_ne_zero (p.map M.ι) hmap (-(N : ℤ))
      (by omega)
    have hC : (algebraMap M.K (LaurentSeries M.K)).comp M.ι = ι₀ := RingHom.ext fun x => by
      rw [RingHom.comp_apply, hι₀, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        HahnSeries.ofPowerSeries_C]
      rfl
    rw [eval₂_map, hC]
    exact hp
  have hρ : (relPolyVia S A φ).eval₂ (eval₂RingHom ι₀ τ) ρ = 0 := by
    rw [eval₂_relPolyVia, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hι₀, hφ, ringHom_aeval_of_complex M.ι M.map_complex]
  have hv : (relPolyVia S A φ).eval₂ (eval₂RingHom (algebraMap B B') X) v = 0 := by
    rw [eval₂_relPolyVia, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [halg, hφ]
  obtain ⟨ι', hι'B, hι'X, hι'v⟩ :=
    exists_ringHom_extension_of_relIrr hXtr htop' _ hirr hv ι₀ hτinj hρ
  have hι'incl : ∀ x, ι' (incl x) = HahnSeries.C (M.ι x) := fun x =>
    RingHom.congr_fun hι'B x
  -- the lead of the branch
  have hρlead : HasLead ρ (-(N : ℤ)) w.σ := by
    have h1 := (hasLead_single (-(R : ℤ)) (1 : M.K)).mul (hasLead_ofPowerSeries z)
    rw [add_zero, one_mul, hz0] at h1
    have h2 := h1.laurentExpand hm
    rw [hρdef]
    convert h2 using 1
    rw [hNdef]
    push_cast
    ring
  set Aser : LaurentSeries M.K := single (N : ℤ) 1 * ι' (incl G * v) with hAser
  have hGv : ι' (incl G * v) = HahnSeries.C (M.ι G) * ρ := by
    rw [map_mul, hι'incl, hι'v]
  have hAlead : HasLead Aser 0 (w.σ * M.ι G) := by
    have h1 := (hasLead_single (N : ℤ) (1 : M.K)).mul ((hasLead_C (M.ι G)).mul hρlead)
    rw [hAser, hGv]
    convert h1 using 1
    · ring
    · ring
  have hAτ : Aser * τ = ι' (incl G * v) := by
    rw [hAser, hτdef, mul_comm, ← mul_assoc, single_mul_single, neg_add_cancel, mul_one,
      ← C_apply, map_one, one_mul]
  -- differentiality
  let D : B' → LaurentSeries M.K := fun x => levelTime M.δK N Aser (ι' x) - ι' (δB' x)
  have hadd : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    simp only [D, map_add]
    ring
  have hmul : ∀ x y, D (x * y) = ι' x * D y + ι' y * D x := by
    intro x y
    simp only [D, map_mul, Derivation.leibniz, smul_eq_mul, map_add]
    ring
  have hF : ∀ c : B, D (algebraMap B B' c) = 0 := by
    intro c
    simp only [D, halg, hincl, hι'incl, levelTime_C, M.map_deriv, sub_self]
  have hDX : D X = 0 := by
    simp only [D, hι'X, hX']
    rw [← hAτ, hτdef, levelTime_single_neg hN, sub_self]
  have hD := twisted_eq_zero_of_relIrr hXtr htop' _ hirr.ne_zero hv ι' D hadd hmul hF hDX
  refine ⟨⟨R, hR, Aser, ι', hι'incl, hι'X, hAlead, hAτ.symm,
    fun x => (sub_eq_zero.mp (hD x)).symm, fun c => ?_⟩⟩
  rw [← incl.commutes c, hι'incl, M.map_complex, LaurentDerivation.algebraMap_complex_laurent]

/-! ## The next model -/

namespace CascadeModel.StepData

variable {M : CascadeModel B δB rat j} {B' : Type} [Field B'] [Algebra ℂ B']
  {δB' : Derivation ℂ B' B'} {incl : B →ₐ[ℂ] B'} {G : B} {X v : B'} {A₀ : M.K} {m : ℕ}

local instance laurentCharZero (K : Type) [Field K] [Algebra ℂ K] :
    CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (LaurentSeries K)).injective

/-- The algebraic closure of the new Laurent layer. -/
abbrev Closure (_D : M.StepData δB' incl G X v A₀ m) : Type :=
  AlgebraicClosure (LaurentSeries M.K)

/-- The time derivation of the layer, extended to the algebraic closure. -/
def timeExt (D : M.StepData δB' incl G X v A₀ m) : Derivation ℂ D.Closure D.Closure :=
  Classical.choose (exists_derivation_algebraicClosure (levelTime M.δK (D.R * m) D.Aser))

theorem timeExt_algebraMap (D : M.StepData δB' incl G X v A₀ m) (y : LaurentSeries M.K) :
    D.timeExt (algebraMap (LaurentSeries M.K) D.Closure y) =
      algebraMap (LaurentSeries M.K) D.Closure (levelTime M.δK (D.R * m) D.Aser y) :=
  Classical.choose_spec (exists_derivation_algebraicClosure (levelTime M.δK (D.R * m) D.Aser)) y

/-- The coordinate derivations of the layer, extended to the algebraic closure. -/
def coordExt (D : M.StepData δB' incl G X v A₀ m) (i : Fin (j + 1)) :
    Derivation ℂ D.Closure D.Closure :=
  Classical.choose (exists_derivation_algebraicClosure (levelCoord M.pK (D.R * m) i))

theorem coordExt_algebraMap (D : M.StepData δB' incl G X v A₀ m) (i : Fin (j + 1))
    (y : LaurentSeries M.K) :
    D.coordExt i (algebraMap (LaurentSeries M.K) D.Closure y) =
      algebraMap (LaurentSeries M.K) D.Closure (levelCoord M.pK (D.R * m) i y) :=
  Classical.choose_spec (exists_derivation_algebraicClosure (levelCoord M.pK (D.R * m) i)) y

/-- **The model of the next cascade field.** -/
@[reducible] def model (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) : CascadeModel B' δB' rat' (j + 1) where
  K := D.Closure
  δK := D.timeExt
  pK := D.coordExt
  ι := (algebraMap (LaurentSeries M.K) D.Closure).comp D.ι'
  map_deriv x := by
    rw [RingHom.comp_apply, RingHom.comp_apply, D.map_deriv, timeExt_algebraMap]
  map_complex c := by
    rw [RingHom.comp_apply, D.map_complex, ← IsScalarTower.algebraMap_apply]
  coord_rat i r := by
    rw [RingHom.comp_apply, coordExt_algebraMap, hrat, D.map_incl]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [levelCoord_last_C, map_zero]
    · rw [levelCoord_castSucc_C, M.coord_rat, map_zero, map_zero]

theorem model_ι (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (x : B') :
    (D.model rat' hrat).ι x = algebraMap (LaurentSeries M.K) D.Closure (D.ι' x) := rfl

/-- Jacobians of Laurent elements in the next model are images of Laurent-level Jacobians. -/
theorem model_det (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (Y : LaurentSeries M.K) :
    (Matrix.of fun r i : Fin (j + 1) => (D.model rat' hrat).pK i
      ((((D.model rat' hrat).δK : D.Closure → D.Closure)^[(r : ℕ)])
        (algebraMap (LaurentSeries M.K) D.Closure Y))).det =
      algebraMap (LaurentSeries M.K) D.Closure
        (Matrix.of fun r i : Fin (j + 1) => levelCoord M.pK (D.R * m) i
          (((levelTime M.δK (D.R * m) D.Aser : LaurentSeries M.K → LaurentSeries M.K)^[(r : ℕ)])
            Y)).det :=
  (map_derivationJacobian_det (algebraMap (LaurentSeries M.K) D.Closure) _ _
    (fun i => ⇑(levelCoord M.pK (D.R * m) i)) (fun i => ⇑(D.coordExt i))
    (fun y => (D.timeExt_algebraMap y).symm) (fun i y => (D.coordExt_algebraMap i y).symm)
    Y).symm

theorem model_det_ne_zero (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (Y : LaurentSeries M.K)
    (hY : (Matrix.of fun r i : Fin (j + 1) => levelCoord M.pK (D.R * m) i
      (((levelTime M.δK (D.R * m) D.Aser : LaurentSeries M.K → LaurentSeries M.K)^[(r : ℕ)])
        Y)).det ≠ 0) :
    (Matrix.of fun r i : Fin (j + 1) => (D.model rat' hrat).pK i
      ((((D.model rat' hrat).δK : D.Closure → D.Closure)^[(r : ℕ)])
        (algebraMap (LaurentSeries M.K) D.Closure Y))).det ≠ 0 := by
  rw [model_det]
  exact (_root_.map_ne_zero _).mpr hY

/-- **Top Jacobian.**  The new state has nonzero Jacobian in the next model as soon as the constant
term of its logarithmic velocity has nonzero Jacobian in the present one. -/
theorem model_top (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (hm : m ≠ 0)
    (hlow : (Matrix.of fun r i : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)]) A₀)).det ≠ 0) :
    (Matrix.of fun r i : Fin (j + 1) => (D.model rat' hrat).pK i
      ((((D.model rat' hrat).δK : D.Closure → D.Closure)^[(r : ℕ)])
        ((D.model rat' hrat).ι X))).det ≠ 0 := by
  have hN : D.R * m ≠ 0 := Nat.mul_ne_zero D.R_ne hm
  rw [model_ι, D.map_X]
  apply model_det_ne_zero
  cases j with
  | zero =>
      exact levelJacobian_one_ne_zero M.δK hN D.Aser M.pK (hasLead_single _ (1 : M.K))
        one_ne_zero (by omega)
  | succ j' =>
      exact levelJacobian_top_ne_zero M.δK M.pK hN D.lead hlow

/-- The three nonvanishings behind `model_wimanLead`. -/
theorem model_wimanLead_aux (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (hm : m ≠ 0) (hA₀ : A₀ ≠ 0) {τ' : LaurentSeries ℂ}
    {k' : ℤ} {c' : ℂ} (hτlead : HasLead τ' k' c') (hk : k' < m) (hc : c' ≠ 0) :
    let σ := algebraMap (LaurentSeries M.K) D.Closure (laurentBaseChange M.K D.R D.R_ne τ')
    σ * (D.model rat' hrat).ι (incl G * v) ≠ 0 ∧
    ((∀ lam : ℂ, lam ≠ 0 → (Matrix.of fun r i : Fin j => M.pK i
        (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.δK A₀ / A₀ + algebraMap ℂ M.K lam * A₀))).det ≠ 0) →
      (Matrix.of fun r i : Fin (j + 1) => (D.model rat' hrat).pK i
        ((((D.model rat' hrat).δK : D.Closure → D.Closure)^[(r : ℕ)])
          (σ * (D.model rat' hrat).ι (incl G * v)))).det ≠ 0) ∧
    ((∀ lam : ℂ, lam ≠ 0 → (Matrix.of fun r i : Fin j => M.pK i
        (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.δK A₀ / A₀ + algebraMap ℂ M.K lam * A₀))).det ≠ 0) →
      ∀ lam : ℂ, lam ≠ 0 → (Matrix.of fun r i : Fin (j + 1) => (D.model rat' hrat).pK i
        ((((D.model rat' hrat).δK : D.Closure → D.Closure)^[(r : ℕ)])
          ((D.model rat' hrat).δK (σ * (D.model rat' hrat).ι (incl G * v)) /
              (σ * (D.model rat' hrat).ι (incl G * v)) +
            algebraMap ℂ D.Closure lam * (σ * (D.model rat' hrat).ι (incl G * v))))).det ≠ 0) := by
  intro σ
  have hN : D.R * m ≠ 0 := Nat.mul_ne_zero D.R_ne hm
  have halg : ∀ c : ℂ, algebraMap (LaurentSeries M.K) D.Closure
      (algebraMap ℂ (LaurentSeries M.K) c) = algebraMap ℂ D.Closure c :=
    fun c => (IsScalarTower.algebraMap_apply ℂ (LaurentSeries M.K) D.Closure c).symm
  obtain ⟨W, hWdef⟩ : ∃ W : LaurentSeries M.K,
      W = laurentBaseChange M.K D.R D.R_ne τ' * D.ι' (incl G * v) := ⟨_, rfl⟩
  have hRpos : (0 : ℤ) < D.R := by exact_mod_cast Nat.pos_of_ne_zero D.R_ne
  obtain ⟨w, hwdef⟩ : ∃ w : ℤ, w = (D.R : ℤ) * k' + -((D.R * m : ℕ) : ℤ) := ⟨_, rfl⟩
  have hw : w < 0 := by
    rw [hwdef]
    push_cast
    nlinarith
  have hWlead : HasLead W w (algebraMap ℂ M.K c' * A₀) := by
    have h1 := hτlead.laurentBaseChange (K := M.K) D.R_ne
    have h2 : HasLead (D.ι' (incl G * v)) (-((D.R * m : ℕ) : ℤ)) A₀ := by
      rw [D.map_Gv]
      have := D.lead.mul (hasLead_single (-((D.R * m : ℕ) : ℤ)) (1 : M.K))
      rwa [zero_add, mul_one] at this
    rw [hWdef, hwdef]
    exact h1.mul h2
  have hc' : algebraMap ℂ M.K c' * A₀ ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr hc) hA₀
  have hW0 : W ≠ 0 := hWlead.ne_zero hc'
  have hσι : σ * (D.model rat' hrat).ι (incl G * v) =
      algebraMap (LaurentSeries M.K) D.Closure W := by
    rw [model_ι, hWdef, map_mul (algebraMap (LaurentSeries M.K) D.Closure)]
  have hlam : ((-w : ℤ) : ℂ) / ((D.R * m : ℕ) : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (by omega : -w ≠ 0)
    · exact_mod_cast hN
  refine ⟨?_, fun hstep => ?_, fun hstep lam hlam0 => ?_⟩
  · rw [hσι]
    exact (_root_.map_ne_zero _).mpr hW0
  · have hlower : (Matrix.of fun r i : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)])
        (M.δK A₀ / A₀ + ((-w : ℤ) : M.K) / ((D.R * m : ℕ) : M.K) * A₀))).det ≠ 0 := by
      have h := hstep _ hlam
      rwa [map_div₀, map_intCast, map_natCast] at h
    rw [hσι]
    apply model_det_ne_zero
    cases j with
    | zero =>
        exact levelJacobian_one_ne_zero M.δK hN D.Aser M.pK hWlead hc' hw.ne
    | succ j' =>
        have h := levelJacobian_step_ne_zero M.δK M.pK hN D.lead hA₀ hw c' hc hWlead hlower
          one_ne_zero 1 one_ne_zero
        rwa [Derivation.map_one_eq_zero, zero_mul, zero_add, map_one, map_one, one_mul] at h
  · have hlower : (Matrix.of fun r i : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)])
        (M.δK A₀ / A₀ + ((-w : ℤ) : M.K) / ((D.R * m : ℕ) : M.K) * A₀))).det ≠ 0 := by
      have h := hstep _ hlam
      rwa [map_div₀, map_intCast, map_natCast] at h
    have harg : (D.model rat' hrat).δK (algebraMap (LaurentSeries M.K) D.Closure W) /
          algebraMap (LaurentSeries M.K) D.Closure W +
        algebraMap ℂ D.Closure lam * algebraMap (LaurentSeries M.K) D.Closure W =
        algebraMap (LaurentSeries M.K) D.Closure
          (levelTime M.δK (D.R * m) D.Aser W * W⁻¹ +
            HahnSeries.C (algebraMap ℂ M.K lam) * W) := by
      change D.timeExt _ / _ + _ = _
      rw [timeExt_algebraMap, ← halg, LaurentDerivation.algebraMap_complex_laurent,
        map_add (algebraMap (LaurentSeries M.K) D.Closure),
        map_mul (algebraMap (LaurentSeries M.K) D.Closure),
        map_mul (algebraMap (LaurentSeries M.K) D.Closure),
        map_inv₀ (algebraMap (LaurentSeries M.K) D.Closure), div_eq_mul_inv]
    rw [hσι, harg]
    apply model_det_ne_zero
    cases j with
    | zero =>
        have hY := hasLead_levelTime_logDeriv_add M.δK (D.R * m) D.lead hW0 hWlead hw
          (algebraMap ℂ M.K lam)
        exact levelJacobian_one_ne_zero M.δK hN D.Aser M.pK hY
          (mul_ne_zero ((_root_.map_ne_zero _).mpr hlam0) hc') hw.ne
    | succ j' =>
        exact levelJacobian_step_ne_zero M.δK M.pK hN D.lead hA₀ hw c' hc hWlead hlower hW0
          lam hlam0

/-- **The next Wiman lead.**  Let the next layer relation `(S', A', d')` have a Wiman root `τ'` of
its top symbol at `U = s^(-m)` over `ℂ((s))`, of degree `k' < m` and lead `c' ≠ 0`.  Its base change
`s ↦ t^R` is a Wiman lead at the next model, and both Jacobian nonvanishings propagate. -/
noncomputable def model_wimanLead (D : M.StepData δB' incl G X v A₀ m) (rat' : RatFunc ℂ →+* B')
    (hrat : ∀ r, rat' r = incl (rat r)) (hm : m ≠ 0) (hA₀ : A₀ ≠ 0)
    (hstep : ∀ lam : ℂ, lam ≠ 0 → (Matrix.of fun r i : Fin j => M.pK i
      (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.δK A₀ / A₀ + algebraMap ℂ M.K lam * A₀))).det ≠ 0)
    {S' : Finset (ℕ × ℕ)} {A' : ℕ × ℕ → Polynomial ℂ} {d' : ℕ} {i₀ : ℕ × ℕ}
    (hi₀ : i₀ ∈ firstOrderTopNewtonFace S' A' d') {τ' : LaurentSeries ℂ} {k' : ℤ} {c' : ℂ}
    (hτroot : (topSymbolAt S' A' d' (single (-(m : ℤ)) (1 : ℂ))).IsRoot τ')
    (hτlead : HasLead τ' k' c') (hk : k' < m) (hc : c' ≠ 0) :
    (D.model rat' hrat).WimanLead S' A' d' X (incl G * v) where
  σ := algebraMap (LaurentSeries M.K) D.Closure (laurentBaseChange M.K D.R D.R_ne τ')
  isRoot := by
    have h1 : (topSymbolAt S' A' d' (laurentBaseChange M.K D.R D.R_ne
        (single (-(m : ℤ)) (1 : ℂ)))).IsRoot (laurentBaseChange M.K D.R D.R_ne τ') := by
      rw [topSymbolAt_map _ (laurentBaseChange_algebraMap D.R_ne)]
      exact hτroot.map
    rw [laurentBaseChange_single, map_one,
      show (D.R : ℤ) * -(m : ℤ) = -((D.R * m : ℕ) : ℤ) by push_cast; ring] at h1
    rw [model_ι, D.map_X, topSymbolAt_map (algebraMap (LaurentSeries M.K) D.Closure)
      (fun c => (IsScalarTower.algebraMap_apply ℂ (LaurentSeries M.K) D.Closure c).symm)]
    exact h1.map
  topSymbol_ne := by
    rw [model_ι, D.map_X, topSymbolAt_map (algebraMap (LaurentSeries M.K) D.Closure)
      (fun c => (IsScalarTower.algebraMap_apply ℂ (LaurentSeries M.K) D.Closure c).symm)]
    exact Polynomial.map_ne_zero (topSymbolAt_single_ne_zero S' A' d' i₀ hi₀ ((D.R * m : ℕ) : ℤ)
      (by exact_mod_cast Nat.mul_ne_zero D.R_ne hm))
  lead_ne := (model_wimanLead_aux D rat' hrat hm hA₀ hτlead hk hc).1
  jac_top := (model_wimanLead_aux D rat' hrat hm hA₀ hτlead hk hc).2.1 hstep
  jac_step := (model_wimanLead_aux D rat' hrat hm hA₀ hτlead hk hc).2.2 hstep

end CascadeModel.StepData

/-! ## Nonzero roots of top symbols -/

/-- Over an algebraically closed field, a polynomial with two nonzero coefficients has a nonzero
root: otherwise it would split as `c X^k`. -/
theorem exists_ne_zero_isRoot_of_two_coeff {K : Type*} [Field K] [IsAlgClosed K] {p : K[X]}
    {a b : ℕ} (hab : a ≠ b) (ha : p.coeff a ≠ 0) (hb : p.coeff b ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ p.IsRoot r := by
  by_contra hnot
  push Not at hnot
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact ha (coeff_zero a)
  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hrep : p.roots = Multiset.replicate p.natDegree 0 := by
    refine Multiset.eq_replicate.mpr ⟨hcard, fun r hr => ?_⟩
    by_contra hr0
    exact hnot r hr0 ((mem_roots hp0).mp hr)
  have heq := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hrep, Multiset.map_replicate, Multiset.prod_replicate, map_zero, sub_zero] at heq
  have hcoeff : ∀ c, p.coeff c ≠ 0 → c = p.natDegree := by
    intro c hc
    rw [← heq, coeff_C_mul_X_pow] at hc
    by_contra hne
    exact hc (if_neg hne)
  exact hab ((hcoeff a ha).trans (hcoeff b hb).symm)

/-- The coefficient of the top symbol at the derivative exponent of a top-face index. -/
theorem coeff_topSymbolAt {K : Type} [Field K] [Algebra ℂ K] {S : Finset (ℕ × ℕ)}
    {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ} {i₀ : ℕ × ℕ} (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d)
    (u : K) : (topSymbolAt S A d u).coeff i₀.2 = aeval u (A i₀) := by
  classical
  simp only [topSymbolAt, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single_of_mem i₀ hi₀]
  · rw [if_pos rfl, mul_one]
  · intro i hi hne
    rw [if_neg, mul_zero]
    intro hsnd
    apply hne
    have hiDeg := (Finset.mem_filter.mp hi).2.1
    have hi₀Deg := (Finset.mem_filter.mp hi₀).2.1
    exact Prod.ext (by omega) hsnd.symm

/-- **A nonzero top-symbol root.**  At a value `u` transcendental over `ℂ`, a top face with two
distinct derivative exponents gives the top symbol a nonzero root. -/
theorem exists_ne_zero_isRoot_topSymbolAt {K : Type} [Field K] [Algebra ℂ K] [IsAlgClosed K]
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ} {i₁ i₂ : ℕ × ℕ}
    (hi₁ : i₁ ∈ firstOrderTopNewtonFace S A d) (hi₂ : i₂ ∈ firstOrderTopNewtonFace S A d)
    (h12 : i₁.2 ≠ i₂.2) {u : K} (hu : Transcendental ℂ u) :
    topSymbolAt S A d u ≠ 0 ∧ ∃ σ : K, σ ≠ 0 ∧ (topSymbolAt S A d u).IsRoot σ := by
  have hne : ∀ i ∈ firstOrderTopNewtonFace S A d, aeval u (A i) ≠ 0 := fun i hi h0 =>
    hu ⟨A i, (Finset.mem_filter.mp hi).2.2, h0⟩
  have h1 : (topSymbolAt S A d u).coeff i₁.2 ≠ 0 := by
    rw [coeff_topSymbolAt hi₁]
    exact hne i₁ hi₁
  have h2 : (topSymbolAt S A d u).coeff i₂.2 ≠ 0 := by
    rw [coeff_topSymbolAt hi₂]
    exact hne i₂ hi₂
  refine ⟨fun h0 => h1 (by rw [h0, Polynomial.coeff_zero]),
    exists_ne_zero_isRoot_of_two_coeff h12 h1 h2⟩

/-! ## From the model Jacobian to algebraic independence -/

/-- **Jacobian criterion in a model.**  If the Jacobian `det(∂_i δ^r ι(X))` of a model is nonzero,
the first `j` derivatives of `X` are algebraically independent over the clock field `ℂ(z)`. -/
theorem CascadeModel.algebraicIndependent_iterate (M : CascadeModel B δB rat j) (X : B)
    (h : (Matrix.of fun r i : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.ι X))).det ≠ 0) :
    letI : Algebra (RatFunc ℂ) B := rat.toAlgebra
    AlgebraicIndependent (RatFunc ℂ) (fun r : Fin j => ((δB : B → B)^[(r : ℕ)]) X) := by
  letI algB : Algebra (RatFunc ℂ) B := rat.toAlgebra
  letI algK : Algebra (RatFunc ℂ) M.K := (M.ι.comp rat).toAlgebra
  let ιA : B →ₐ[RatFunc ℂ] M.K := { M.ι with commutes' := fun _ => rfl }
  have hiter : ∀ r : ℕ, M.ι (((δB : B → B)^[r]) X) = ((M.δK : M.K → M.K)^[r]) (M.ι X) := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', M.map_deriv, ih]
  have hind : AlgebraicIndependent (RatFunc ℂ)
      (fun r : Fin j => M.ι (((δB : B → B)^[(r : ℕ)]) X)) := by
    refine algebraicIndependent_of_domain_jacobian (K := RatFunc ℂ) (R := M.K) _
      (fun i => ⇑(M.pK i)) (fun i a b => map_add _ a b) (fun i a b => ?_) (fun i c => ?_)
      (Matrix.of fun i r : Fin j => M.pK i (((M.δK : M.K → M.K)^[(r : ℕ)]) (M.ι X))) ?_
      (fun i r => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    · exact M.coord_rat i c
    · rw [← Matrix.det_transpose]
      convert h using 2
      ext r i
      rfl
    · rw [Matrix.of_apply, hiter]
  exact AlgebraicIndependent.of_comp ιA hind

end

end GaloisForLFunctions.HTGeometry
