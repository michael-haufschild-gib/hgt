import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity

/-!
# Integrality acts only on the torsion

When can integrality force a small integer auxiliary to vanish **exactly** at a return of the prime
orbit? The value `A(it) = F((p^{-it})_p)` of an integer auxiliary is the value of `F` at the orbit
point, and the orbit point is not algebraic.

* **No-go at generic heights** (`countable_setOf_exists_orbitValue_eq_zero`). A nonzero integer
  auxiliary is the restriction of the entire function `A(s) = Σ_α c_α e^{−s λ_α}`,
  `λ_α = Σ_p α_p log p`, whose frequencies are distinct (unique factorization), so it is not
  identically zero (`exists_orbitFun_ne_zero`) and vanishes at countably many heights
  (`countable_setOf_orbitValue_eq_zero`). There are countably many integer auxiliaries, so the
  heights at which **some** nonzero integer auxiliary on `P` vanishes form a countable set.
* **Every return window contains generic heights** (`exists_return_forall_orbitValue_ne_zero`). The
  `δ`-returns to a torsion point form a nonempty open set, so they contain a height at which no
  nonzero integer auxiliary vanishes: integrality cannot turn the forced near-vanishing at returns
  into zeros.
* **The survivor: repulsion at sign returns** (`one_sub_le_norm_orbitValue`). At a sign vector
  `ε ∈ {±1}^P` the value `F(ε) = Σ_n a_n ε(n)` is an integer, so at every `δ`-return to `ε` where
  `F(ε) ≠ 0`, `|A(it)| ≥ 1 − δ L(F)`. At a torsion point of order `m` the same holds for the product
  over the Frobenius orbit (`one_le_prod_frobeniusOrbit`). Integrality on the orbit is a lower bound,
  not a source of zeros.
-/

open Finset Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open InfiniteRankWeilTheory

variable {P : Finset Nat.Primes}

/-- The frequency `λ_α = Σ_p α_p log p` of the monomial `u^α`, the logarithm of `n = Π p^{α_p}`. -/
def frequency (α : P →₀ ℕ) : ℝ := ∑ p : P, (α p : ℝ) * Real.log ((p : Nat.Primes) : ℕ)

/-- Unique factorization: distinct exponent vectors have distinct frequencies. -/
theorem frequency_injective : Function.Injective (frequency (P := P)) := by
  intro α β h
  have hli := primeLogFiniteSlice_linearIndependent P
  have hz : ∑ p : P, ((α p : ℚ) - β p) • Real.log ((p : Nat.Primes) : ℕ) = 0 := by
    have : frequency α - frequency β = 0 := sub_eq_zero.mpr h
    rw [frequency, frequency, ← sum_sub_distrib] at this
    rw [← this]
    refine sum_congr rfl fun p _ => ?_
    rw [Rat.smul_def]
    push_cast
    ring
  ext p
  have := linearIndependent_iff'.mp hli univ _ hz p (mem_univ p)
  have h' : (α p : ℚ) = β p := sub_eq_zero.mp this
  exact_mod_cast h'

/-- The entire function `A(s) = F((p^{-s})_p)`. -/
def orbitFun (F : MvPolynomial P ℤ) (s : ℂ) : ℂ :=
  MvPolynomial.aeval (fun p : P => cexp (-s * Real.log ((p : Nat.Primes) : ℕ))) F

theorem orbitFun_eq_sum (F : MvPolynomial P ℤ) (s : ℂ) :
    orbitFun F s = ∑ α ∈ F.support, ((F.coeff α : ℤ) : ℂ) * cexp (-s * frequency α) := by
  rw [orbitFun, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine sum_congr rfl fun α _ => ?_
  rw [algebraMap_int_eq, eq_intCast]
  congr 1
  simp only [← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 1
  unfold frequency
  push_cast
  rw [mul_sum, ← sum_subset (subset_univ α.support)
    (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp]; simp)]
  refine sum_congr rfl fun p _ => ?_
  ring

theorem differentiable_orbitFun (F : MvPolynomial P ℤ) : Differentiable ℂ (orbitFun F) := by
  have : orbitFun F = fun s => ∑ α ∈ F.support, ((F.coeff α : ℤ) : ℂ) * cexp (-s * frequency α) :=
    funext (orbitFun_eq_sum F)
  rw [this]
  fun_prop

/-- On the imaginary axis the entire function is the orbit value. -/
theorem orbitFun_I_mul (F : MvPolynomial P ℤ) (t : ℝ) : orbitFun F (t * I) = orbitValue F t := by
  rw [orbitFun, orbitValue]
  have h : (fun p : P => cexp (-((t : ℂ) * I) * Real.log ((p : Nat.Primes) : ℕ))) =
      orbitPoint P t := by
    funext p
    rw [orbitPoint, phase]
    congr 1
    push_cast
    ring
  rw [h]

/-- **A nonzero integer auxiliary is not identically zero.** On the real axis the term of smallest
frequency dominates. -/
theorem exists_orbitFun_ne_zero {F : MvPolynomial P ℤ} (hF : F ≠ 0) : ∃ s, orbitFun F s ≠ 0 := by
  classical
  have hne : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  obtain ⟨α₀, hα₀, hmin⟩ := F.support.exists_min_image frequency hne
  have hc₀ : ((F.coeff α₀ : ℤ) : ℂ) ≠ 0 := by exact_mod_cast MvPolynomial.mem_support_iff.mp hα₀
  set R := F.support.erase α₀
  have hgap : ∀ α ∈ R, 0 < frequency α - frequency α₀ := by
    intro α hα
    have hne' : α ≠ α₀ := ne_of_mem_erase hα
    have hle := hmin α (mem_of_mem_erase hα)
    have : frequency α ≠ frequency α₀ := fun h => hne' (frequency_injective h)
    exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm this))
  -- `e^{σλ₀} A(σ) = c₀ + Σ_{α ≠ α₀} c_α e^{−σ(λ_α − λ₀)} → c₀`
  have htend : Filter.Tendsto (fun σ : ℝ => ∑ α ∈ R,
      ‖((F.coeff α : ℤ) : ℂ)‖ * Real.exp (-(σ * (frequency α - frequency α₀)))) Filter.atTop
      (nhds 0) := by
    have : (0 : ℝ) = ∑ α ∈ R, ‖((F.coeff α : ℤ) : ℂ)‖ * 0 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun α hα => (tendsto_const_nhds.mul ?_)
    exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.atTop_mul_const (hgap α hα)))
  obtain ⟨σ, hσ⟩ := (htend.eventually (gt_mem_nhds (norm_pos_iff.mpr hc₀))).exists
  refine ⟨σ, fun h0 => ?_⟩
  have hsplit : orbitFun F σ * cexp (σ * frequency α₀) = ((F.coeff α₀ : ℤ) : ℂ) +
      ∑ α ∈ R, ((F.coeff α : ℤ) : ℂ) * cexp (-(σ * (frequency α - frequency α₀))) := by
    rw [orbitFun_eq_sum, ← add_sum_erase _ _ hα₀, add_mul, sum_mul]
    congr 1
    · rw [mul_assoc, ← Complex.exp_add]; simp
    · refine sum_congr rfl fun α _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
  rw [h0, zero_mul] at hsplit
  have hb : ‖∑ α ∈ R, ((F.coeff α : ℤ) : ℂ) * cexp (-(σ * (frequency α - frequency α₀)))‖ ≤
      ∑ α ∈ R, ‖((F.coeff α : ℤ) : ℂ)‖ * Real.exp (-(σ * (frequency α - frequency α₀))) := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun α _ => ?_)
    rw [norm_mul]
    refine le_of_eq ?_
    congr 1
    rw [show (-((σ : ℂ) * ((frequency α : ℂ) - frequency α₀))) =
      ((-(σ * (frequency α - frequency α₀)) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
  have heq : ((F.coeff α₀ : ℤ) : ℂ) = -∑ α ∈ R, ((F.coeff α : ℤ) : ℂ) * cexp (-(σ * (frequency α -
      frequency α₀))) := eq_neg_of_add_eq_zero_left hsplit.symm
  have : ‖((F.coeff α₀ : ℤ) : ℂ)‖ ≤ ∑ α ∈ R, ‖((F.coeff α : ℤ) : ℂ)‖ *
      Real.exp (-(σ * (frequency α - frequency α₀))) := by
    rw [heq, norm_neg]; exact hb
  linarith

/-- A nonzero integer auxiliary vanishes at countably many heights. -/
theorem countable_setOf_orbitValue_eq_zero {F : MvPolynomial P ℤ} (hF : F ≠ 0) :
    {t : ℝ | orbitValue F t = 0}.Countable := by
  obtain ⟨s, hs⟩ := exists_orbitFun_ne_zero hF
  have hc := RHTower.WeilConditional.countable_setOf_eq_zero_of_differentiable
    (differentiable_orbitFun F) hs
  have hinj : Function.Injective (fun t : ℝ => (t : ℂ) * I) := by
    intro a b h
    have := congrArg Complex.im h
    simpa using this
  refine (hc.preimage hinj).mono fun t ht => ?_
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at ht ⊢
  rw [orbitFun_I_mul]
  exact ht

/-- **No-go at generic heights.** The heights at which some nonzero integer auxiliary on `P`
vanishes form a countable set. -/
theorem countable_setOf_exists_orbitValue_eq_zero (P : Finset Nat.Primes) :
    {t : ℝ | ∃ F : MvPolynomial P ℤ, F ≠ 0 ∧ orbitValue F t = 0}.Countable := by
  haveI : Countable (MvPolynomial P ℤ) := by
    refine Function.Injective.countable (f := fun F : MvPolynomial P ℤ =>
      Finsupp.onFinset F.support (fun α => F.coeff α)
        (fun α h => MvPolynomial.mem_support_iff.mpr h)) ?_
    intro F G h
    ext α
    have := DFunLike.congr_fun h α
    simpa using this
  have : {t : ℝ | ∃ F : MvPolynomial P ℤ, F ≠ 0 ∧ orbitValue F t = 0} =
      ⋃ F : {F : MvPolynomial P ℤ // F ≠ 0}, {t : ℝ | orbitValue F.1 t = 0} := by
    ext t
    simp
  rw [this]
  exact Set.countable_iUnion fun F => countable_setOf_orbitValue_eq_zero F.2

/-- **Every return window contains a generic height.** For every torsion point `ζ_m^b` and every
`δ > 0` there is a `δ`-return at which no nonzero integer auxiliary on `P` vanishes. -/
theorem exists_return_forall_orbitValue_ne_zero (P : Finset Nat.Primes) (m : ℕ) (b : P → ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, (∀ p : P, ‖orbitPoint P t p - cexp (2 * Real.pi * I / m) ^ b p‖ < δ) ∧
      ∀ F : MvPolynomial P ℤ, F ≠ 0 → orbitValue F t ≠ 0 := by
  set U := {t : ℝ | ∀ p : P, ‖orbitPoint P t p - cexp (2 * Real.pi * I / m) ^ b p‖ < δ}
  have hUo : IsOpen U := by
    have : U = ⋂ p : P, {t : ℝ | ‖orbitPoint P t p - cexp (2 * Real.pi * I / m) ^ b p‖ < δ} := by
      ext t; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun p => isOpen_lt ?_ continuous_const
    refine Continuous.norm (Continuous.sub ?_ continuous_const)
    simp only [orbitPoint, phase]
    fun_prop
  obtain ⟨t₀, -, ht₀⟩ := exists_torsion_return P b hδ 0
  have hUne : U.Nonempty := ⟨t₀, ht₀⟩
  have hpos := hUo.measure_pos MeasureTheory.volume hUne
  by_contra hcon
  push Not at hcon
  have hsub : U ⊆ {t : ℝ | ∃ F : MvPolynomial P ℤ, F ≠ 0 ∧ orbitValue F t = 0} := by
    intro t ht
    obtain ⟨F, hF, h⟩ := hcon t ht
    exact ⟨F, hF, h⟩
  have h0 := ((countable_setOf_exists_orbitValue_eq_zero P).mono hsub).measure_zero
    MeasureTheory.volume
  exact hpos.ne' h0

/-- **Repulsion at sign returns.** At a `δ`-return to a sign vector `ε` with `F(ε) ≠ 0`, the
integer auxiliary satisfies `|A(it)| ≥ 1 − δ L(F)`. -/
theorem one_sub_le_norm_orbitValue (F : MvPolynomial P ℤ) (ε : P → ℂ) (hε : ∀ p, ε p = 1 ∨ ε p = -1)
    (hF : MvPolynomial.aeval ε F ≠ 0) {t δ : ℝ} (hret : ∀ p, ‖orbitPoint P t p - ε p‖ ≤ δ) :
    1 - δ * lipWeight F ≤ ‖orbitValue F t‖ := by
  have hεn : ∀ p, ‖ε p‖ ≤ 1 := fun p => by rcases hε p with h | h <;> simp [h]
  have hint : ∃ z : ℤ, MvPolynomial.aeval ε F = z := by
    have hεint : ∀ p, ∃ z : ℤ, ε p = z := fun p => by
      rcases hε p with h | h
      · exact ⟨1, by simp [h]⟩
      · exact ⟨-1, by simp [h]⟩
    choose z hz using hεint
    refine ⟨MvPolynomial.aeval z F, ?_⟩
    have : ε = fun p => ((z p : ℤ) : ℂ) := funext hz
    rw [this]
    have h := MvPolynomial.comp_aeval_apply (R := ℤ) (f := z) (Algebra.ofId ℤ ℂ) F
    simp only [eq_intCast] at h
    exact h.symm
  obtain ⟨z, hz⟩ := hint
  have hz1 : 1 ≤ ‖MvPolynomial.aeval ε F‖ := by
    rw [hz, Complex.norm_intCast]
    have : z ≠ 0 := by rintro rfl; exact hF (by rw [hz]; simp)
    exact_mod_cast Int.one_le_abs this
  have hL := norm_aeval_sub_le F (u := orbitPoint P t) (fun p => (norm_phase _ _).le) hεn hret
  have htri := norm_sub_norm_le (MvPolynomial.aeval ε F) (MvPolynomial.aeval (orbitPoint P t) F)
  rw [norm_sub_rev] at htri
  rw [orbitValue]
  linarith

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
