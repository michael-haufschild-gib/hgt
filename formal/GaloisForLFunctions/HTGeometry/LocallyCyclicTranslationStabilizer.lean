import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative
import GaloisForLFunctions.HTGeometry.EntireExponentialCompositionDA
import GaloisForLFunctions.HTGeometry.EntireMultiplicativeTranslationDefectCountability
import GaloisForLFunctions.HTGeometry.GapExponentialCarrier
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial
import GaloisForLFunctions.HTGeometry.LadderPrimeFrequencies

/-!
# Exact differential-algebraic translation stabilizers

The set of shifts whose translation defect satisfies an algebraic differential equation is an
additive subgroup of `ℂ`.  For the exponential carrier of a superlacunary gap series with nonzero
coefficients it is computed exactly: a defect is differentially algebraic precisely when the phase
`exp(β h)` is eventually a `b_k`-th root of unity, and this is a tail-divisibility condition on the
denominator of `h/α`.  Feeding a denominator ladder into the frequency construction realizes an
arbitrary subgroup of `ℚ` containing `1`, hence — after scaling by any nonzero `α` — every nonzero
locally cyclic subgroup of `ℂ`, including the dense proper subgroup `ℚ` itself.  The same subgroup
is the multiplicative stabilizer of the zero-free exponential of the carrier.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The additive differential-algebraic translation stabilizer. -/
def daTranslationStabilizer (F : ℂ → ℂ) : Set ℂ :=
  {h : ℂ | DifferentiallyAlgebraic fun z => F (z + h) - F z}

/-- The multiplicative differential-algebraic translation stabilizer. -/
def daMultiplicativeStabilizer (G : ℂ → ℂ) : Set ℂ :=
  {h : ℂ | DifferentiallyAlgebraic fun z => G (z + h) / G z}

/-- Every finitely generated subgroup is cyclic. -/
def IsLocallyCyclic (H : AddSubgroup ℂ) : Prop :=
  ∀ T : Finset ℂ, (T : Set ℂ) ⊆ (H : Set ℂ) →
    ∃ g : ℂ, AddSubgroup.closure (T : Set ℂ) = AddSubgroup.zmultiples g

/-- The phase of a shift returns to `1` at order `n` exactly when the shift is an integer multiple
of `α` after scaling by `n`. -/
theorem expPhase_pow_eq_one_iff {α : ℂ} (hα : α ≠ 0) (n : ℕ) (h : ℂ) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I / α) * h) ^ n = 1
      ↔ ∃ m : ℤ, (n : ℂ) * h = (m : ℂ) * α := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    field_simp at hm
    linear_combination hm
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    field_simp
    linear_combination hm

/-! ### The carrier attached to a ladder -/

variable {a b : ℕ → ℕ}

/-- The coefficient sequence used by the realization: reciprocal factorials on the frequencies. -/
def ladderCoeff (b : ℕ → ℕ) (k : ℕ) : ℂ := 1 / (((b k).factorial : ℕ) : ℂ)

theorem ladderCoeff_ne_zero (b : ℕ → ℕ) (k : ℕ) : ladderCoeff b k ≠ 0 := by
  rw [ladderCoeff, div_ne_zero_iff]
  exact ⟨one_ne_zero, Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)⟩

theorem norm_ladderCoeff (b : ℕ → ℕ) (k : ℕ) :
    ‖ladderCoeff b k‖ = 1 / (((b k).factorial : ℕ) : ℝ) := by
  rw [ladderCoeff, norm_div, norm_one, Complex.norm_natCast]

theorem entireCoeffs_gapCoeff_ladderCoeff (hinj : Function.Injective b) :
    EntireCoeffs (gapCoeff b (ladderCoeff b)) :=
  entireCoeffs_gapCoeff hinj fun k => le_of_eq (norm_ladderCoeff b k)

/-- **The stabilizer of an exponential gap carrier**, in the phase form. -/
theorem mem_daTranslationStabilizer_expGapFun_iff (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1)) {β : ℂ} (hβ : β ≠ 0) (h : ℂ) :
    h ∈ daTranslationStabilizer (expGapFun b (ladderCoeff b) β)
      ↔ ∃ K : ℕ, ∀ k, K ≤ k → Complex.exp (β * h) ^ (b k) = 1 :=
  differentiallyAlgebraic_expGapFun_defect_iff hstrict hgap
    (entireCoeffs_gapCoeff_ladderCoeff hstrict.injective) (ladderCoeff_ne_zero b) hβ h

/-! ### Realizing a subgroup of the rationals -/

/-- **Exact realization for a rational line.**  For every nonzero `α` and every subgroup `S` of `ℚ`
containing `1`, the scaled copy of `S` is the exact differential-algebraic translation stabilizer of
an entire `α`-periodic hypertranscendental function. -/
theorem exists_daTranslationStabilizer_eq_ratLine {α : ℂ} (hα : α ≠ 0) (S : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ S) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Function.Periodic F α ∧ Hypertranscendental F ∧
      daTranslationStabilizer F = {h : ℂ | ∃ q ∈ S, h = (q : ℂ) * α} := by
  obtain ⟨a, hapos, hastep, haS⟩ := exists_denLadder S h1
  obtain ⟨b, hstrict, hbpos, hgap, hdvd⟩ := exists_ladderFrequencies hapos hastep
  have hEC := entireCoeffs_gapCoeff_ladderCoeff (b := b) hstrict.injective
  set β : ℂ := 2 * (Real.pi : ℂ) * Complex.I / α with hβdef
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hβ : β ≠ 0 := div_ne_zero hpi hα
  refine ⟨expGapFun b (ladderCoeff b) β, ?_, ?_, ?_, ?_⟩
  · show Differentiable ℂ fun z => gapFun b (ladderCoeff b) (Complex.exp (β * z))
    exact (differentiable_gapFun hEC).comp
      (((differentiable_const β).mul differentiable_id).cexp)
  · have hper := periodic_comp_exp (gapFun b (ladderCoeff b)) hβ
    have hval : 2 * (Real.pi : ℂ) * Complex.I / β = α := by
      rw [hβdef]
      field_simp
    rwa [hval] at hper
  · refine hypertranscendental_expGapFun hstrict hgap hEC ?_ hβ
    have hset : {k : ℕ | ladderCoeff b k ≠ 0} = Set.univ := by
      ext k
      simp [ladderCoeff_ne_zero b k]
    rw [hset]
    exact Set.infinite_univ
  · ext h
    rw [mem_daTranslationStabilizer_expGapFun_iff hstrict hgap hβ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨K, hK⟩
      have hbK : (((b K : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hbpos K).ne'
      obtain ⟨m, hm⟩ := (expPhase_pow_eq_one_iff hα (b K) h).1 (by rw [← hβdef] at *; exact hK K le_rfl)
      set q : ℚ := (m : ℚ) / (((b K : ℕ)) : ℚ) with hq
      have hcast : ((q : ℚ) : ℂ) = (m : ℂ) / (((b K : ℕ)) : ℂ) := by
        rw [hq]; push_cast; ring
      have hqh : h = (q : ℂ) * α := by
        rw [hcast, div_mul_eq_mul_div, ← hm]
        field_simp
      have hden : ∀ k, K ≤ k → q.den ∣ b k := by
        intro k hk
        obtain ⟨m', hm'⟩ := (expPhase_pow_eq_one_iff hα (b k) h).1
          (by rw [← hβdef] at *; exact hK k hk)
        have hcancel : (((b k : ℕ)) : ℂ) * (q : ℂ) = (m' : ℂ) := by
          rw [hqh, ← mul_assoc] at hm'
          exact mul_right_cancel₀ hα hm'
        have hQ : (((b k : ℕ)) : ℚ) * q = (m' : ℚ) := by
          have hc : ((((((b k : ℕ)) : ℚ) * q) : ℚ) : ℂ) = (((m' : ℚ)) : ℂ) := by
            push_cast
            exact hcancel
          exact_mod_cast hc
        exact (exists_intCast_natMul_iff_den_dvd (hbpos k) q).1 ⟨m', hQ⟩
      obtain ⟨K', hK'⟩ := (hdvd q.den q.den_pos).2 ⟨K, hden⟩
      exact ⟨q, (haS q).2 ⟨K', hK'⟩, hqh⟩
    · rintro ⟨q, hqS, rfl⟩
      obtain ⟨K, hK⟩ := (haS q).1 hqS
      obtain ⟨N, hN⟩ := (hdvd q.den q.den_pos).1 ⟨K, hK⟩
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨m, hm⟩ := (exists_intCast_natMul_iff_den_dvd (hbpos k) q).2 (hN k hk)
      rw [hβdef]
      refine (expPhase_pow_eq_one_iff hα (b k) _).2 ⟨m, ?_⟩
      have hc : (((b k : ℕ)) : ℂ) * (q : ℂ) = (m : ℂ) := by
        have := congrArg (fun x : ℚ => (x : ℂ)) hm
        push_cast at this
        exact this
      rw [← mul_assoc, hc]

/-- **The exact `ℚ` instance.**  There is an entire `1`-periodic hypertranscendental function whose
differential-algebraic translation stabilizer is exactly the dense proper subgroup `ℚ ⊆ ℂ`. -/
theorem exists_daTranslationStabilizer_eq_rat :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Function.Periodic F 1 ∧ Hypertranscendental F ∧
      daTranslationStabilizer F = {h : ℂ | ∃ q : ℚ, h = (q : ℂ)} := by
  obtain ⟨F, hd, hper, hht, hst⟩ :=
    exists_daTranslationStabilizer_eq_ratLine one_ne_zero ⊤ (AddSubgroup.mem_top _)
  refine ⟨F, hd, hper, hht, ?_⟩
  rw [hst]
  ext h
  simp

/-- A nonzero locally cyclic subgroup of `ℂ` is a rational line through any of its nonzero
elements. -/
theorem eq_ratLine_of_locallyCyclic {H : AddSubgroup ℂ} (hlc : IsLocallyCyclic H) {α : ℂ}
    (hαH : α ∈ H) (hα : α ≠ 0) {h : ℂ} (hh : h ∈ H) : ∃ q : ℚ, h = (q : ℂ) * α := by
  classical
  obtain ⟨g, hg⟩ := hlc ({α, h} : Finset ℂ) (by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hαH, hh])
  have hcoe : (({α, h} : Finset ℂ) : Set ℂ) = {α, h} := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
  have hαz : α ∈ AddSubgroup.zmultiples g := by
    rw [← hg]
    exact AddSubgroup.subset_closure (by rw [hcoe]; exact Set.mem_insert _ _)
  have hhz : h ∈ AddSubgroup.zmultiples g := by
    rw [← hg]
    exact AddSubgroup.subset_closure (by rw [hcoe]; exact Set.mem_insert_of_mem _ rfl)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hαz
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hhz
  rw [zsmul_eq_mul] at hm hn
  have hm0 : (m : ℂ) ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hm
    exact hα hm.symm
  refine ⟨(n : ℚ) / (m : ℚ), ?_⟩
  have hcast : (((n : ℚ) / (m : ℚ) : ℚ) : ℂ) = (n : ℂ) / (m : ℂ) := by push_cast; ring
  rw [hcast, ← hm, ← hn]
  field_simp

/-- **Exact realization of every nonzero locally cyclic subgroup.**  Every nonzero locally cyclic
additive subgroup of `ℂ` is the exact differential-algebraic translation stabilizer of an entire
hypertranscendental function. -/
theorem exists_daTranslationStabilizer_eq_of_locallyCyclic {H : AddSubgroup ℂ}
    (hlc : IsLocallyCyclic H) {α : ℂ} (hαH : α ∈ H) (hα : α ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Function.Periodic F α ∧ Hypertranscendental F ∧
      daTranslationStabilizer F = (H : Set ℂ) := by
  set S : AddSubgroup ℚ :=
    { carrier := {q : ℚ | ((q : ℂ) * α) ∈ H}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Rat.cast_add, add_mul]
        exact H.add_mem hx hy
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        rw [Rat.cast_neg, neg_mul]
        exact H.neg_mem hx } with hS
  have h1 : (1 : ℚ) ∈ S := by
    show ((1 : ℚ) : ℂ) * α ∈ H
    simpa using hαH
  obtain ⟨F, hd, hper, hht, hst⟩ := exists_daTranslationStabilizer_eq_ratLine hα S h1
  refine ⟨F, hd, hper, hht, ?_⟩
  rw [hst]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    obtain ⟨q, rfl⟩ := eq_ratLine_of_locallyCyclic hlc hαH hα hx
    exact ⟨q, hx, rfl⟩

/-! ### The stabilizer as a subgroup, and the tail description -/

/-- **The differential-algebraic translation stabilizer of an entire function is an additive
subgroup**, by the cocycle identity `Δ_{x+y} = (Δ_y)(·+x) + Δ_x` and its negative counterpart. -/
def daTranslationSubgroup {F : ℂ → ℂ} (hF : Differentiable ℂ F) : AddSubgroup ℂ where
  carrier := daTranslationStabilizer F
  zero_mem' := by
    show DifferentiallyAlgebraic fun z => F (z + 0) - F z
    have hz : (fun z => F (z + 0) - F z) = fun _ : ℂ => (0 : ℂ) := by
      funext z
      rw [add_zero, sub_self]
    rw [hz]
    exact differentiallyAlgebraic_const 0
  add_mem' := by
    intro x y hx hy
    show DifferentiallyAlgebraic fun z => F (z + (x + y)) - F z
    have h1 : DifferentiallyAlgebraic (fun z => F (z + x + y) - F (z + x)) :=
      (show DifferentiallyAlgebraic fun z => F (z + y) - F z from hy).comp_add_const x
    have h2 : DifferentiallyAlgebraic (fun z => F (z + x) - F z) := hx
    have hA1 : AnalyticOnNhd ℂ (fun z => F (z + x + y) - F (z + x)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2
        ((hF.comp ((differentiable_id.add_const x).add_const y)).sub
          (hF.comp (differentiable_id.add_const x)))
    have hA2 : AnalyticOnNhd ℂ (fun z => F (z + x) - F z) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2
        ((hF.comp (differentiable_id.add_const x)).sub hF)
    have hsum : (fun z => F (z + (x + y)) - F z)
        = fun z => (F (z + x + y) - F (z + x)) + (F (z + x) - F z) := by
      funext z
      rw [show z + (x + y) = z + x + y by ring]
      ring
    rw [hsum]
    exact differentiallyAlgebraic_add hA1 hA2 h1 h2
  neg_mem' := by
    intro x hx
    show DifferentiallyAlgebraic fun z => F (z + -x) - F z
    have h1 : DifferentiallyAlgebraic (fun z => F (z + -x + x) - F (z + -x)) :=
      (show DifferentiallyAlgebraic fun z => F (z + x) - F z from hx).comp_add_const (-x)
    have hA1 : AnalyticOnNhd ℂ (fun z => F (z + -x + x) - F (z + -x)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2
        ((hF.comp ((differentiable_id.add_const (-x)).add_const x)).sub
          (hF.comp (differentiable_id.add_const (-x))))
    have hA0 : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2 (differentiable_const 0)
    have hEq : (fun z => F (z + -x) - F z)
        = fun z => (0 : ℂ) - (F (z + -x + x) - F (z + -x)) := by
      funext z
      rw [show z + -x + x = z by ring]
      ring
    rw [hEq]
    exact differentiallyAlgebraic_sub hA0 hA1 (differentiallyAlgebraic_const 0) h1

@[simp] theorem mem_daTranslationSubgroup {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h : ℂ) :
    h ∈ daTranslationSubgroup hF ↔ DifferentiallyAlgebraic fun z => F (z + h) - F z := Iff.rfl

/-- **The tail description of the stabilizer.**  For an exponential gap carrier with eventually
superlacunary frequencies the stabilizer is the increasing union of the eventual-period groups: the
shift `h` is admissible exactly when `b_k · h` is an integer multiple of `α` for every large `k`. -/
theorem daTranslationStabilizer_expGapFun_eq (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1)) {α : ℂ} (hα : α ≠ 0) :
    daTranslationStabilizer (expGapFun b (ladderCoeff b) (2 * (Real.pi : ℂ) * Complex.I / α))
      = ⋃ N : ℕ, {h : ℂ | ∀ k, N ≤ k → ∃ m : ℤ, ((b k : ℕ) : ℂ) * h = (m : ℂ) * α} := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  ext h
  rw [mem_daTranslationStabilizer_expGapFun_iff hstrict hgap (div_ne_zero hpi hα), Set.mem_iUnion]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun k hk => (expPhase_pow_eq_one_iff hα (b k) h).1 (hK k hk)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun k hk => (expPhase_pow_eq_one_iff hα (b k) h).2 (hN k hk)⟩

/-- **The finite-or-hypertranscendental dichotomy.**  A translation defect of an exponential gap
carrier is either a finite exponential sum or hypertranscendental; no infinite differentially
algebraic defect occurs. -/
theorem expGapFun_defect_finite_or_hypertranscendental (hstrict : StrictMono b)
    (hgap : ∀ C : ℕ, ∀ᶠ k in atTop, C * b k < b (k + 1)) {β : ℂ} (hβ : β ≠ 0) (h : ℂ) :
    (∃ K : ℕ, (fun z => expGapFun b (ladderCoeff b) β (z + h)
        - expGapFun b (ladderCoeff b) β z)
      = fun z => ∑ k ∈ Finset.range K,
          (ladderCoeff b k * (Complex.exp (β * h) ^ (b k) - 1))
            * Complex.exp ((β * ((b k : ℕ) : ℂ)) * z))
    ∨ Hypertranscendental (fun z => expGapFun b (ladderCoeff b) β (z + h)
        - expGapFun b (ladderCoeff b) β z) := by
  classical
  by_cases hcase : ∃ K : ℕ, ∀ k, K ≤ k → Complex.exp (β * h) ^ (b k) = 1
  · obtain ⟨K, hK⟩ := hcase
    refine Or.inl ⟨K, ?_⟩
    rw [expGapFun_translationDefect hstrict.injective
      (entireCoeffs_gapCoeff_ladderCoeff hstrict.injective) β h]
    exact expGapFun_eq_finsetSum (c := fun k => ladderCoeff b k * (Complex.exp (β * h) ^ (b k) - 1))
      hstrict.injective (K := K) (fun k hk => by rw [hK k hk, sub_self, mul_zero]) β
  · exact Or.inr fun hDA => hcase
      ((differentiallyAlgebraic_expGapFun_defect_iff hstrict hgap
        (entireCoeffs_gapCoeff_ladderCoeff hstrict.injective) (ladderCoeff_ne_zero b) hβ h).1 hDA)

/-! ### The multiplicative form -/

/-- **Multiplicative realization.**  The same subgroup is the exact stabilizer of the multiplicative
translation defect of a zero-free entire hypertranscendental function. -/
theorem exists_daMultiplicativeStabilizer_eq_ratLine {α : ℂ} (hα : α ≠ 0) (S : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ S) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G z ≠ 0) ∧ Hypertranscendental G ∧
      daMultiplicativeStabilizer G = {h : ℂ | ∃ q ∈ S, h = (q : ℂ) * α} := by
  obtain ⟨F, hd, -, hht, hst⟩ := exists_daTranslationStabilizer_eq_ratLine hα S h1
  refine ⟨fun z => Complex.exp (F z), hd.cexp, fun z => Complex.exp_ne_zero _, ?_, ?_⟩
  · intro hDA
    have hG : AnalyticOnNhd ℂ (fun z => Complex.exp (F z)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2 hd.cexp
    have hlog := (differentiallyAlgebraic_logDeriv_iff hG
      (fun z => Complex.exp_ne_zero _)).2 hDA
    have hderiv : (fun z => deriv (fun z => Complex.exp (F z)) z / Complex.exp (F z))
        = deriv F := by
      funext z
      rw [(((hd z).hasDerivAt).cexp).deriv]
      field_simp
    rw [hderiv] at hlog
    exact hht (differentiallyAlgebraic_of_deriv hlog)
  · rw [← hst]
    ext h
    have hquot : (fun z => Complex.exp (F (z + h)) / Complex.exp (F z))
        = fun z => Complex.exp (F (z + h) - F z) := by
      funext z
      rw [Complex.exp_sub]
    show DifferentiallyAlgebraic (fun z => Complex.exp (F (z + h)) / Complex.exp (F z)) ↔ _
    rw [hquot]
    constructor
    · intro hDA
      set u : ℂ → ℂ := fun z => F (z + h) - F z with hu
      have hud : Differentiable ℂ u :=
        (hd.comp (differentiable_id.add_const h)).sub hd
      have hK : AnalyticOnNhd ℂ (fun z => Complex.exp (u z)) Set.univ :=
        Complex.analyticOnNhd_univ_iff_differentiable.2 hud.cexp
      have hlog := (differentiallyAlgebraic_logDeriv_iff hK
        (fun z => Complex.exp_ne_zero _)).2 hDA
      have hderiv : (fun z => deriv (fun z => Complex.exp (u z)) z / Complex.exp (u z))
          = deriv u := by
        funext z
        rw [(((hud z).hasDerivAt).cexp).deriv]
        field_simp
      rw [hderiv] at hlog
      exact differentiallyAlgebraic_of_deriv hlog
    · intro hDA
      refine differentiallyAlgebraic_cexp_comp ?_ hDA
      exact Complex.analyticOnNhd_univ_iff_differentiable.2
        ((hd.comp (differentiable_id.add_const h)).sub hd)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The `ℚ` stabilizer is proper and non-discrete -/

/-- **The dense proper example.**  The rational stabilizer is a proper subgroup of `ℂ` containing
nonzero shifts of arbitrarily small size: differential-algebraic constraints exist at shifts
accumulating at `0` while the function and every off-subgroup defect stay hypertranscendental. -/
theorem exists_daTranslationStabilizer_eq_rat_proper_accumulating :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Function.Periodic F 1 ∧ Hypertranscendental F ∧
      daTranslationStabilizer F = {h : ℂ | ∃ q : ℚ, h = (q : ℂ)} ∧
      daTranslationStabilizer F ≠ Set.univ ∧
      ∀ ε : ℝ, 0 < ε → ∃ h ∈ daTranslationStabilizer F, h ≠ 0 ∧ ‖h‖ < ε := by
  obtain ⟨F, hd, hper, hht, hst⟩ := exists_daTranslationStabilizer_eq_rat
  refine ⟨F, hd, hper, hht, hst, ?_, ?_⟩
  · intro huniv
    have hI : Complex.I ∈ daTranslationStabilizer F := by rw [huniv]; trivial
    rw [hst] at hI
    obtain ⟨q, hq⟩ := hI
    have him : Complex.I.im = 0 := by rw [hq, Complex.ratCast_im]
    rw [Complex.I_im] at him
    exact one_ne_zero him
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨((1 / ((n : ℚ) + 1) : ℚ) : ℂ), ?_, ?_, ?_⟩
    · rw [hst]
      exact ⟨1 / ((n : ℚ) + 1), rfl⟩
    · rw [Ne, Rat.cast_eq_zero]
      exact (by positivity : (0 : ℚ) < 1 / ((n : ℚ) + 1)).ne'
    · rw [Complex.norm_ratCast]
      have hval : ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; ring
      rw [hval, abs_of_pos (by positivity)]
      exact hn

end

end GaloisForLFunctions.HTGeometry
