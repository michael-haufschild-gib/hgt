import GaloisForLFunctions.CurvesOverFiniteFields.Genus
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Data.Int.LeastGreatest

/-!
# Weil differentials and the Riemann–Roch theorem

A Weil differential of level `D` is an `F`-linear functional on `K` vanishing on `I(D) + J(D)`
(`weilSpace D`). Thus `Ω(D)` is the dual of `H¹(D)` and `dim Ω(D) = h¹(D)` (`finrank_weilSpace`).
Functions act on functionals by `(x·ω)(f) = ω(x f)` (`smulDual`).

* `h¹(D) = 0` once `deg D` is large (`exists_hOne_eq_zero`): some `D₀` has `I(D₀) + J(D₀) = K`,
  and a nonzero `x ∈ L(D − D₀)`, supplied by Riemann's inequality, carries `K` into
  `I(D) + J(D)`.
* Two nonzero Weil differentials are proportional over `K` (`exists_eq_smulDual`): otherwise
  `L(A₁ + B) × L(A₂ + B)` embeds into `Ω(−B)`, which Riemann's theorem forbids for an effective
  `B` of large degree.
* A nonzero differential has a largest level `W`, its canonical divisor (`exists_canonical`):
  levels have bounded degree, and a level `D` exceeding `W` at a place `P` makes `W + P` a level,
  because `I(W + P) ⊆ I(W) + I(D)` (`finSpace_raiseFin_le`).
* **Riemann–Roch** (`riemann_roch`): `x ↦ x·ω` is an isomorphism `L(W − D) ≅ Ω(D)`
  (`hOne_eq_ell_sub`), hence `ℓ(D) − ℓ(W − D) = deg D + 1 − g`, `deg W = 2g − 2` and `ℓ(W) = g`.
-/

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A nonzero element has valuation different from one at only finitely many places. -/
theorem finite_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite R x).union
    (HeightOneSpectrum.Support.finite R x⁻¹)).subset fun v hv => ?_
  have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hl : log (v.valuation K x) ≠ 0 := by
    intro h
    apply hv
    rw [← exp_log hv0, h, exp_zero]
  rcases lt_or_gt_of_ne hl with h | h
  · apply Set.mem_union_right
    change 1 < v.valuation K x⁻¹
    rw [map_inv₀, ← exp_log hv0, ← exp_neg, ← exp_zero, exp_lt_exp]
    omega
  · apply Set.mem_union_left
    change 1 < v.valuation K x
    rw [← exp_log hv0, ← exp_zero, exp_lt_exp]
    exact h

/-- The pole orders `v ↦ log v(x)` of a nonzero element, as a finitely supported function. -/
def valDiv {x : K} (hx : x ≠ 0) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => log (v.valuation K x)) (by
    refine (finite_valuation_ne_one hx).subset fun v hv => ?_
    show v.valuation K x ≠ 1
    intro h
    apply hv
    change log (v.valuation K x) = 0
    rw [h, log_one])

theorem valDiv_apply {x : K} (hx : x ≠ 0) (v : HeightOneSpectrum R) :
    valDiv hx v = log (v.valuation K x) := rfl

/-- Valuation spaces multiply. -/
theorem mul_mem_valSpace {E E' : HeightOneSpectrum R →₀ ℤ} {x f : K} (hx : x ∈ valSpace K E)
    (hf : f ∈ valSpace K E') : x * f ∈ valSpace K (E + E') := fun v => by
  rw [map_mul, Finsupp.add_apply, exp_add]
  exact mul_le_mul' (hx v) (hf v)

/-- Dividing by a nonzero `x` shifts valuation spaces by its pole orders. -/
theorem mem_valSpace_add_valDiv_iff {x : K} (hx : x ≠ 0) {E : HeightOneSpectrum R →₀ ℤ}
    {f : K} : f ∈ valSpace K (E + valDiv hx) ↔ x⁻¹ * f ∈ valSpace K E := by
  simp only [mem_valSpace, Finsupp.add_apply, valDiv_apply]
  refine forall_congr' fun v => ?_
  by_cases hf : f = 0
  · simp [hf]
  have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hf0 : v.valuation K f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  obtain ⟨a, ha⟩ : ∃ a, v.valuation K x = exp a := ⟨_, (exp_log hv0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, v.valuation K f = exp b := ⟨_, (exp_log hf0).symm⟩
  rw [map_mul, map_inv₀, ha, hb, log_exp, ← exp_neg, ← exp_add, exp_le_exp, exp_le_exp]
  omega

/-- Every element lies in some valuation space. -/
theorem exists_mem_valSpace (f : K) : ∃ E : HeightOneSpectrum R →₀ ℤ, f ∈ valSpace K E := by
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) f
  have hk' : f * algebraMap R K d = algebraMap R K n := hk
  have hd0 : algebraMap R K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
  refine ⟨-valDiv hd0, fun v => ?_⟩
  have hv0 : v.valuation K (algebraMap R K d) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  have hf : f = algebraMap R K n * (algebraMap R K d)⁻¹ := by
    rw [← hk', mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  rw [hf, map_mul, map_inv₀, Finsupp.neg_apply, valDiv_apply, exp_neg, exp_log hv0]
  exact mul_le_of_le_one_left' (v.valuation_le_one (K := K) n)

/-- Raising `E` at a place `v` where `E'` exceeds it stays inside `V(E) + V(E')`: an element of
`V(E + v)` with exact pole order at `v`, chosen in `V(E')`, generates `V(E + v)/V(E)`. -/
theorem valSpace_raise_le_sup {E E' : HeightOneSpectrum R →₀ ℤ} {v : HeightOneSpectrum R}
    (hv : E v < E' v) : valSpace K (E + Finsupp.single v 1) ≤ valSpace K E ⊔ valSpace K E' := by
  classical
  intro f hf
  have hEv : (E ⊓ E') v = E v := by rw [Finsupp.inf_apply, inf_of_le_left hv.le]
  obtain ⟨h, hh, hhv⟩ := exists_mem_raise_valuation_eq (K := K) (E ⊓ E') v
  have hEW : E ⊓ E' + Finsupp.single v 1 ≤ E + Finsupp.single v 1 := by
    rw [Finsupp.le_def]
    intro w
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.inf_apply]
    omega
  have hED : E ⊓ E' + Finsupp.single v 1 ≤ E' := by
    rw [Finsupp.le_def]
    intro w
    rw [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with hw
    · subst hw
      rw [hEv]
      omega
    · rw [add_zero, Finsupp.inf_apply]
      exact inf_le_right
  have hhW := valSpace_mono (K := K) hEW hh
  have hhD := valSpace_mono (K := K) hED hh
  rw [hEv] at hhv
  obtain ⟨r, hr⟩ := exists_sub_smul_mem_valSpace (K := K) E v hhW hhv hf
  have hsum := Submodule.add_mem _ (Submodule.mem_sup_left (T := valSpace K E') hr)
    (Submodule.mem_sup_right (S := valSpace K E) ((valSpace K E').smul_mem r hhD))
  rwa [sub_add_cancel] at hsum

end General

section SmulDual

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Multiplication of a functional by a function: `(x·ω)(f) = ω(x f)`. -/
def smulDual (ω : Module.Dual F K) : K →ₗ[F] Module.Dual F K where
  toFun x := ω ∘ₗ LinearMap.mulLeft F x
  map_add' x y := by ext f; simp [add_mul]
  map_smul' c x := by ext f; simp

theorem smulDual_apply (ω : Module.Dual F K) (x f : K) : smulDual ω x f = ω (x * f) := rfl

theorem smulDual_eq_zero_iff {ω : Module.Dual F K} (hω : ω ≠ 0) {x : K} :
    smulDual ω x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    apply hω
    ext f
    have := LinearMap.congr_fun h (x⁻¹ * f)
    rw [smulDual_apply, ← mul_assoc, mul_inv_cancel₀ hx, one_mul, LinearMap.zero_apply] at this
    rw [this, LinearMap.zero_apply]
  · rintro rfl
    exact map_zero _

end SmulDual

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)] {K : Type*} [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

section Divisors

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_add (D D' : Divisor F K) : (D + D').deg = D.deg + D'.deg := by
  simp only [Divisor.deg, Prod.fst_add, Prod.snd_add]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)]
  ring

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_zero : (0 : Divisor F K).deg = 0 := by
  simp [Divisor.deg]

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_neg (D : Divisor F K) : (-D).deg = -D.deg := by
  have h := deg_add (-D) D
  rw [neg_add_cancel, deg_zero] at h
  linarith

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_single_fin (P : FinPlace F K) (n : ℤ) :
    Divisor.deg ((Finsupp.single P n, 0) : Divisor F K) = n * finDeg F K P := by
  simp only [Divisor.deg, Finsupp.sum_zero_index, add_zero]
  rw [Finsupp.sum_single_index (by simp)]

omit [IsScalarTower F (RatFunc F) K] in
theorem finSpace_mono {D D' : Divisor F K} (h : D ≤ D') : finSpace D ≤ finSpace D' :=
  fun _ hf => valSpace_mono (K := K) (Prod.le_def.mp h).1 hf

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
theorem infSpace_mono {D D' : Divisor F K} (h : D ≤ D') : infSpace D ≤ infSpace D' :=
  fun _ hf => valSpace_mono (K := K) (Prod.le_def.mp h).2 hf

omit [IsScalarTower F (RatFunc F) K] in
theorem mul_mem_finSpace {E E' : Divisor F K} {x f : K} (hx : x ∈ finSpace E)
    (hf : f ∈ finSpace E') : x * f ∈ finSpace (E + E') :=
  mul_mem_valSpace (K := K) (R := finChart F K) hx hf

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
theorem mul_mem_infSpace {E E' : Divisor F K} {x f : K} (hx : x ∈ infSpace E)
    (hf : f ∈ infSpace E') : x * f ∈ infSpace (E + E') :=
  mul_mem_valSpace (K := K) (R := infChart F K) hx hf

/-- The divisor of poles and zeros of a nonzero function: `v ↦ log v(x)` at every place. -/
def pdiv {x : K} (hx : x ≠ 0) : Divisor F K :=
  (valDiv (R := finChart F K) hx, valDiv (R := infChart F K) hx)

omit [DecidableEq (RatFunc F)] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] [Algebra F K]
  [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
/-- A finite place exists: the finite chart is not a field. -/
theorem nonempty_finPlace : Nonempty (FinPlace F K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (finChart F K)
  exact ⟨⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (FunctionField.ringOfIntegers.not_isField F K)⟩⟩

end Divisors

section Weil

/-- Weil differentials of level `D`: functionals on `K` vanishing on `I(D) + J(D)`. -/
abbrev weilSpace (D : Divisor F K) : Submodule F (Module.Dual F K) :=
  (finSpace D ⊔ infSpace D).dualAnnihilator

/-- `Ω(D)` is the dual of `H¹(D)`: `dim Ω(D) = h¹(D)`. -/
theorem finrank_weilSpace (D : Divisor F K) : Module.finrank F (weilSpace D) = hOne D := by
  rw [← (Submodule.dualQuotEquivDualAnnihilator (finSpace D ⊔ infSpace D)).finrank_eq,
    Subspace.dual_finrank_eq]
  rfl

theorem finiteDimensional_weilSpace {D : Divisor F K} (hD : IsFin D) :
    FiniteDimensional F (weilSpace D) := by
  haveI := hD.2
  exact (Submodule.dualQuotEquivDualAnnihilator (finSpace D ⊔ infSpace D)).finiteDimensional

/-- `x ∈ L(E)` carries Weil differentials of level `A` to level `A − E`. -/
theorem smulDual_mem {A E : Divisor F K} {ω : Module.Dual F K} (hω : ω ∈ weilSpace A) {x : K}
    (hx : x ∈ finSpace E ⊓ infSpace E) : smulDual ω x ∈ weilSpace (A - E) := by
  rw [Submodule.mem_dualAnnihilator] at hω ⊢
  intro f hf
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp hf
  have hA : E + (A - E) = A := by abel
  have h1 : x * f₁ ∈ finSpace A ⊔ infSpace A := by
    refine Submodule.mem_sup_left ?_
    have := mul_mem_finSpace (Submodule.mem_inf.mp hx).1 hf₁
    rwa [hA] at this
  have h2 : x * f₂ ∈ finSpace A ⊔ infSpace A := by
    refine Submodule.mem_sup_right ?_
    have := mul_mem_infSpace (Submodule.mem_inf.mp hx).2 hf₂
    rwa [hA] at this
  rw [smulDual_apply, mul_add, map_add, hω _ h1, hω _ h2, add_zero]

/-- Some divisor `D₀ ≥ 0` has `I(D₀) + J(D₀) = K`: lift a finite spanning set of `H¹(0)` and
raise the infinite part until it contains the lifts. -/
theorem exists_sup_eq_top (h0 : IsFin (0 : Divisor F K)) :
    ∃ D₀ : Divisor F K, 0 ≤ D₀ ∧ finSpace D₀ ⊔ infSpace D₀ = ⊤ := by
  classical
  haveI := h0.2
  set U := finSpace (0 : Divisor F K) ⊔ infSpace (0 : Divisor F K)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule F (K ⧸ U)).FG)
  have key : ∀ t : Finset (K ⧸ U), ∃ E : InfPlace F K →₀ ℤ, 0 ≤ E ∧
      ∀ y ∈ t, ∃ f ∈ infSpace ((0, E) : Divisor F K), U.mkQ f = y := by
    intro t
    refine Finset.induction_on t ⟨0, le_rfl, by simp⟩ ?_
    intro a t _ ih
    obtain ⟨E, hE0, hE⟩ := ih
    obtain ⟨f, rfl⟩ := U.mkQ_surjective a
    obtain ⟨E', hE'⟩ := exists_mem_valSpace (R := infChart F K) (K := K) f
    refine ⟨E ⊔ E', le_sup_of_le_left hE0, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨f, valSpace_mono (K := K) le_sup_right hE', rfl⟩
    · obtain ⟨g, hg, rfl⟩ := hE y hy
      exact ⟨g, valSpace_mono (K := K) le_sup_left hg, rfl⟩
  obtain ⟨E, hE0, hE⟩ := key s
  have hD0 : (0 : Divisor F K) ≤ (0, E) := Prod.le_def.mpr ⟨le_rfl, hE0⟩
  set W := finSpace ((0, E) : Divisor F K) ⊔ infSpace ((0, E) : Divisor F K)
  have hUW : U ≤ W := sup_le_sup (finSpace_mono hD0) (infSpace_mono hD0)
  have hmap : ⊤ ≤ W.map U.mkQ := by
    rw [← hs, Submodule.span_le]
    intro y hy
    obtain ⟨f, hf, rfl⟩ := hE y hy
    exact Submodule.mem_map.mpr ⟨f, Submodule.mem_sup_right hf, rfl⟩
  refine ⟨(0, E), hD0, eq_top_iff.mpr fun f _ => ?_⟩
  obtain ⟨w, hw, hwf⟩ := Submodule.mem_map.mp (hmap (Submodule.mem_top : U.mkQ f ∈ ⊤))
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hwf
  have e : f = w - (w - f) := by abel
  rw [e]
  exact W.sub_mem hw (hUW hwf)

omit [IsScalarTower F (RatFunc F) K] in
/-- Raising `W` at a finite place where `D` exceeds it stays inside `I(W) + I(D)`. -/
theorem finSpace_raiseFin_le {W D : Divisor F K} {P : FinPlace F K} (hP : W.1 P < D.1 P) :
    finSpace (raiseFin W P) ≤ finSpace W ⊔ finSpace D := by
  intro f hf
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (valSpace_raise_le_sup (R := finChart F K)
    (K := K) hP (show f ∈ valSpace K (W.1 + Finsupp.single P 1) from hf))
  exact Submodule.add_mem _ (Submodule.mem_sup_left (show y ∈ finSpace W from hy))
    (Submodule.mem_sup_right (show z ∈ finSpace D from hz))

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
/-- Raising `W` at an infinite place where `D` exceeds it stays inside `J(W) + J(D)`. -/
theorem infSpace_raiseInf_le {W D : Divisor F K} {Q : InfPlace F K} (hQ : W.2 Q < D.2 Q) :
    infSpace (raiseInf W Q) ≤ infSpace W ⊔ infSpace D := by
  intro f hf
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (valSpace_raise_le_sup (R := infChart F K)
    (K := K) hQ (show f ∈ valSpace K (W.2 + Finsupp.single Q 1) from hf))
  exact Submodule.add_mem _ (Submodule.mem_sup_left (show y ∈ infSpace W from hy))
    (Submodule.mem_sup_right (show z ∈ infSpace D from hz))

end Weil

variable (hconst : ∀ x : K, IsIntegral F x → ∃ a : F, algebraMap F K a = x)
include hconst

/-- **Vanishing of `H¹` in high degree**: `h¹(D) = 0` whenever `deg D ≥ c`. -/
theorem exists_hOne_eq_zero : ∃ c : ℤ, ∀ D : Divisor F K, c ≤ D.deg → hOne D = 0 := by
  obtain ⟨D₀, -, hD₀⟩ := exists_sup_eq_top (isFin_zero hconst)
  refine ⟨D₀.deg + genus F K, fun D hD => ?_⟩
  have hl := riemann_inequality hconst (D - D₀)
  have hdeg : (D - D₀).deg = D.deg - D₀.deg := by
    have h := deg_add (D - D₀) D₀
    rw [sub_add_cancel] at h
    linarith
  have hpos : (finSpace (D - D₀) ⊓ infSpace (D - D₀) : Submodule F K) ≠ ⊥ := by
    intro hbot
    have h0 : ell (D - D₀) = 0 := by unfold ell; rw [hbot, finrank_bot]
    rw [h0] at hl
    push_cast at hl
    linarith
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  have hDD : (D - D₀) + D₀ = D := sub_add_cancel D D₀
  have htop : finSpace D ⊔ infSpace D = ⊤ := by
    refine eq_top_iff.mpr fun f _ => ?_
    have hf : x⁻¹ * f ∈ finSpace D₀ ⊔ infSpace D₀ := by rw [hD₀]; exact Submodule.mem_top
    obtain ⟨f₁, hf₁, f₂, hf₂, hsum⟩ := Submodule.mem_sup.mp hf
    have e : f = x * f₁ + x * f₂ := by
      rw [← mul_add, hsum, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · have := mul_mem_finSpace (Submodule.mem_inf.mp hx).1 hf₁
      rwa [hDD] at this
    · have := mul_mem_infSpace (Submodule.mem_inf.mp hx).2 hf₂
      rwa [hDD] at this
  haveI : Subsingleton (K ⧸ (finSpace D ⊔ infSpace D)) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact Module.finrank_zero_of_subsingleton

/-- **Two nonzero Weil differentials are proportional over `K`.** -/
theorem exists_eq_smulDual {ω₁ ω₂ : Module.Dual F K} {A₁ A₂ : Divisor F K}
    (h₁ : ω₁ ∈ weilSpace A₁) (h₂ : ω₂ ∈ weilSpace A₂) (hω₁ : ω₁ ≠ 0) :
    ∃ x : K, ω₂ = smulDual ω₁ x := by
  by_contra hno
  push Not at hno
  obtain ⟨P⟩ := nonempty_finPlace (F := F) (K := K)
  set N : ℤ := max (3 * (genus F K : ℤ) - 1 - A₁.deg - A₂.deg) 0 with hNdef
  have hN : 3 * (genus F K : ℤ) - 1 - A₁.deg - A₂.deg ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := le_max_right _ _
  set B : Divisor F K := (Finsupp.single P N, 0) with hBdef
  have hdegB : B.deg = N * finDeg F K P := deg_single_fin P N
  have hP : (1 : ℤ) ≤ finDeg F K P := by
    have := finrank_pos_quotient_place (F := F) P
    unfold finDeg
    omega
  have hNd : N ≤ N * finDeg F K P := le_mul_of_one_le_right hN0 hP
  have hnegB : -B ≤ 0 :=
    Prod.le_def.mpr ⟨neg_nonpos.mpr (Finsupp.single_nonneg.mpr hN0), neg_zero.le⟩
  obtain ⟨hf1, -⟩ := riemann_roch_chi hconst (A₁ + B)
  obtain ⟨hf2, -⟩ := riemann_roch_chi hconst (A₂ + B)
  obtain ⟨hfB, hchiB⟩ := riemann_roch_chi hconst (-B)
  haveI := hf1.1
  haveI := hf2.1
  haveI := finiteDimensional_weilSpace hfB
  have hellB : ell (-B) ≤ 1 := by
    rw [← ell_zero hconst]
    haveI := finiteDimensional_ell_zero hconst
    exact LinearMap.finrank_le_finrank_of_injective
      (f := Submodule.inclusion (inf_le_inf (finSpace_mono hnegB) (infSpace_mono hnegB)))
      (Submodule.inclusion_injective _)
  set L₁ := (finSpace (A₁ + B) ⊓ infSpace (A₁ + B) : Submodule F K)
  set L₂ := (finSpace (A₂ + B) ⊓ infSpace (A₂ + B) : Submodule F K)
  let φ : L₁ × L₂ →ₗ[F] Module.Dual F K :=
    (smulDual ω₁ ∘ₗ L₁.subtype).coprod (smulDual ω₂ ∘ₗ L₂.subtype)
  have hφ : ∀ p : L₁ × L₂, φ p = smulDual ω₁ p.1 + smulDual ω₂ p.2 := fun _ => rfl
  have hmem : ∀ p : L₁ × L₂, φ p ∈ weilSpace (-B) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rw [hφ]
    have e1 : A₁ - (A₁ + B) = -B := by abel
    have e2 : A₂ - (A₂ + B) = -B := by abel
    refine Submodule.add_mem _ ?_ ?_
    · have := smulDual_mem h₁ hx
      rwa [e1] at this
    · have := smulDual_mem h₂ hy
      rwa [e2] at this
  let Φ : L₁ × L₂ →ₗ[F] weilSpace (-B) := LinearMap.codRestrict (weilSpace (-B)) φ hmem
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ h
    have h' : smulDual ω₁ x + smulDual ω₂ y = 0 := congrArg Subtype.val h
    by_cases hy0 : y = 0
    · subst hy0
      rw [map_zero, add_zero, smulDual_eq_zero_iff hω₁] at h'
      subst h'
      rfl
    · exfalso
      apply hno (-(x * y⁻¹))
      ext f
      have := LinearMap.congr_fun h' (y⁻¹ * f)
      rw [LinearMap.add_apply, smulDual_apply, smulDual_apply, LinearMap.zero_apply,
        ← mul_assoc y, mul_inv_cancel₀ hy0, one_mul] at this
      rw [smulDual_apply, neg_mul, map_neg, mul_assoc]
      linear_combination this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, finrank_weilSpace] at hle
  have hle' : ell (A₁ + B) + ell (A₂ + B) ≤ hOne (-B) := hle
  have hle'' : (ell (A₁ + B) : ℤ) + ell (A₂ + B) ≤ hOne (-B) := by exact_mod_cast hle'
  have hellB' : (ell (-B) : ℤ) ≤ 1 := by exact_mod_cast hellB
  have r1 := riemann_inequality hconst (A₁ + B)
  have r2 := riemann_inequality hconst (A₂ + B)
  have d1 := deg_add A₁ B
  have d2 := deg_add A₂ B
  have d3 := deg_neg B
  linarith

/-- **Canonical divisor**: a nonzero Weil differential has a largest level `W`. -/
theorem exists_canonical {ω : Module.Dual F K} (hω : ω ≠ 0) {A : Divisor F K}
    (hA : ω ∈ weilSpace A) :
    ∃ W : Divisor F K, ω ∈ weilSpace W ∧ ∀ D, ω ∈ weilSpace D → D ≤ W := by
  classical
  obtain ⟨c, hc⟩ := exists_hOne_eq_zero hconst
  have hbound : ∀ D, ω ∈ weilSpace D → D.deg < c := by
    intro D hD
    by_contra hlt
    push Not at hlt
    have h0 := hc D hlt
    rw [← finrank_weilSpace] at h0
    haveI := finiteDimensional_weilSpace (riemann_roch_chi hconst D).1
    rw [Submodule.finrank_eq_zero.mp h0] at hD
    exact hω ((Submodule.mem_bot F).mp hD)
  obtain ⟨m, ⟨W, hW, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ D, ω ∈ weilSpace D ∧ D.deg = z)
    ⟨c, fun z hz => by obtain ⟨D, hD, rfl⟩ := hz; exact (hbound D hD).le⟩ ⟨A.deg, A, hA, rfl⟩
  refine ⟨W, hW, fun D hD => ?_⟩
  by_contra hle
  rw [Prod.le_def, not_and_or] at hle
  rcases hle with h | h
  · rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨P, hP⟩ := h
    have hraise : ω ∈ weilSpace (raiseFin W P) := by
      rw [Submodule.mem_dualAnnihilator] at hW hD ⊢
      intro f hf
      obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp (finSpace_raiseFin_le hP hf₁)
      have e1 := hW _ (Submodule.mem_sup_left hg₁)
      have e2 := hD _ (Submodule.mem_sup_left hg₂)
      have e3 := hW _ (Submodule.mem_sup_right (show f₂ ∈ infSpace W from hf₂))
      rw [map_add, map_add, e1, e2, e3, add_zero, add_zero]
    have hm := hmax _ ⟨_, hraise, rfl⟩
    rw [deg_raiseFin] at hm
    have hpos := finrank_pos_quotient_place (F := F) P
    unfold finDeg at hm
    omega
  · rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨Q, hQ⟩ := h
    have hraise : ω ∈ weilSpace (raiseInf W Q) := by
      rw [Submodule.mem_dualAnnihilator] at hW hD ⊢
      intro f hf
      obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp (infSpace_raiseInf_le hQ hf₂)
      have e1 := hW _ (Submodule.mem_sup_left (show f₁ ∈ finSpace W from hf₁))
      have e2 := hW _ (Submodule.mem_sup_right hg₁)
      have e3 := hD _ (Submodule.mem_sup_right hg₂)
      rw [map_add, map_add, e1, e2, e3, add_zero, add_zero]
    have hm := hmax _ ⟨_, hraise, rfl⟩
    rw [deg_raiseInf] at hm
    have hpos := finrank_pos_quotient_place (F := F) Q
    unfold infDeg at hm
    omega

/-- **Duality**: for the canonical divisor `W` of a nonzero `ω`, `x ↦ x·ω` is an isomorphism
`L(W − D) ≅ Ω(D)`, so `h¹(D) = ℓ(W − D)`. Surjectivity: a nonzero `η ∈ Ω(D)` is `x·ω`, then `ω`
has level `D + (x)`, so `D + (x) ≤ W` by maximality, i.e. `x ∈ L(W − D)`. -/
theorem hOne_eq_ell_sub {ω : Module.Dual F K} (hω : ω ≠ 0) {W : Divisor F K}
    (hW : ω ∈ weilSpace W) (hmax : ∀ D, ω ∈ weilSpace D → D ≤ W) (D : Divisor F K) :
    hOne D = ell (W - D) := by
  have hmem : ∀ x : (finSpace (W - D) ⊓ infSpace (W - D) : Submodule F K),
      (smulDual ω ∘ₗ Submodule.subtype _) x ∈ weilSpace D := by
    rintro ⟨x, hx⟩
    have := smulDual_mem hW hx
    rwa [sub_sub_cancel] at this
  let Ψ := LinearMap.codRestrict (weilSpace D) (smulDual ω ∘ₗ Submodule.subtype _) hmem
  have hbij : Function.Bijective Ψ := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      rintro ⟨x, hx⟩ h
      have h' : smulDual ω x = 0 := congrArg Subtype.val h
      rw [smulDual_eq_zero_iff hω] at h'
      subst h'
      rfl
    · rintro ⟨η, hη⟩
      by_cases hη0 : η = 0
      · subst hη0
        exact ⟨0, (map_zero Ψ).trans rfl⟩
      obtain ⟨x, rfl⟩ := exists_eq_smulDual hconst hW hη hω
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hη0 (map_zero _)
      have hlev : ω ∈ weilSpace (D + pdiv hx0) := by
        rw [Submodule.mem_dualAnnihilator] at hη ⊢
        intro g hg
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp hg
        have h1 : x⁻¹ * g₁ ∈ finSpace D :=
          (mem_valSpace_add_valDiv_iff (R := finChart F K) (K := K) (E := D.1) (f := g₁) hx0).mp hg₁
        have h2 : x⁻¹ * g₂ ∈ infSpace D :=
          (mem_valSpace_add_valDiv_iff (R := infChart F K) (K := K) (E := D.2) (f := g₂) hx0).mp hg₂
        have e1 := hη _ (Submodule.mem_sup_left h1)
        have e2 := hη _ (Submodule.mem_sup_right h2)
        rw [smulDual_apply, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at e1 e2
        rw [map_add, e1, e2, add_zero]
      obtain ⟨hle1, hle2⟩ := Prod.le_def.mp (hmax _ hlev)
      have hxL : x ∈ finSpace (W - D) ⊓ infSpace (W - D) := by
        refine Submodule.mem_inf.mpr ⟨fun v => ?_, fun v => ?_⟩
        · have hv := Finsupp.le_def.mp hle1 v
          change D.1 v + log (v.valuation K x) ≤ W.1 v at hv
          have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
          change v.valuation K x ≤ exp ((W - D).1 v)
          rw [← exp_log hv0, exp_le_exp, Prod.fst_sub, Finsupp.sub_apply]
          omega
        · have hv := Finsupp.le_def.mp hle2 v
          change D.2 v + log (v.valuation K x) ≤ W.2 v at hv
          have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
          change v.valuation K x ≤ exp ((W - D).2 v)
          rw [← exp_log hv0, exp_le_exp, Prod.snd_sub, Finsupp.sub_apply]
          omega
      exact ⟨⟨x, hxL⟩, rfl⟩
  rw [← finrank_weilSpace]
  exact ((LinearEquiv.ofBijective Ψ hbij).finrank_eq).symm

/-- **The Riemann–Roch theorem**: there is a divisor `W` (a canonical divisor) such that
`ℓ(D) − ℓ(W − D) = deg D + 1 − g` for every divisor `D`; moreover `deg W = 2g − 2` and
`ℓ(W) = g`. -/
theorem riemann_roch :
    ∃ W : Divisor F K, (∀ D : Divisor F K, (ell D : ℤ) - ell (W - D) = D.deg + 1 - genus F K) ∧
      W.deg = 2 * genus F K - 2 ∧ ell W = genus F K := by
  classical
  obtain ⟨P⟩ := nonempty_finPlace (F := F) (K := K)
  have hdegA := deg_single_fin P (-2)
  obtain ⟨hfA, hchiA⟩ := riemann_roch_chi hconst ((Finsupp.single P (-2), 0) : Divisor F K)
  have hpos : 0 < hOne ((Finsupp.single P (-2), 0) : Divisor F K) := by
    have hP := finrank_pos_quotient_place (F := F) P
    unfold finDeg at hdegA
    have : (0 : ℤ) ≤ ell ((Finsupp.single P (-2), 0) : Divisor F K) := Nat.cast_nonneg _
    omega
  rw [← finrank_weilSpace] at hpos
  haveI := finiteDimensional_weilSpace hfA
  have hne : weilSpace ((Finsupp.single P (-2), 0) : Divisor F K) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨ω, hωA, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨W, hW, hmax⟩ := exists_canonical hconst hω0 hωA
  have hRR : ∀ D, hOne D = ell (W - D) := hOne_eq_ell_sub hconst hω0 hW hmax
  have key : ∀ D : Divisor F K, (ell D : ℤ) - ell (W - D) = D.deg + 1 - genus F K := by
    intro D
    rw [← hRR D]
    exact (riemann_roch_chi hconst D).2
  have hW0 : ell W = genus F K := by
    rw [genus, hRR 0, sub_zero]
  refine ⟨W, key, ?_, hW0⟩
  have h := key W
  rw [sub_self, ell_zero hconst, hW0] at h
  push_cast at h
  linarith

end GaloisForLFunctions.CurvesOverFiniteFields
