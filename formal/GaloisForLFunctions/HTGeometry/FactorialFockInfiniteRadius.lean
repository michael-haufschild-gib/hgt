import Mathlib

/-!
# Factorial Fock energy forces infinite Taylor radius

A square-summable factorial weighting of the coefficients of a formal multilinear series forces
absolute convergence at every radius.  Equivalently, a uniform bound on all finite factorial Fock
energies forces infinite convergence radius.  For a complex function's raw derivative jet, the
coefficient energy `n! * ‖f⁽ⁿ⁾(a) / n!‖²` is exactly `‖f⁽ⁿ⁾(a)‖² / n!`, giving the
cofinal raw-jet criterion used by Gamma-clock constructions.

This is a source-independent analytic bridge.  It does not prove that any arithmetic source has
bounded factorial jet energy, nor does it identify a meromorphic obstruction.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Factorial-Fock infinite-radius law.**  If the squared coefficient norms weighted by `n!`
are summable, a formal multilinear series has infinite convergence radius.  The statement is
vector-valued and works over every nontrivially normed field. -/
theorem radius_eq_top_of_summable_factorialFockEnergy
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F)
    (henergy : Summable (fun n : ℕ => (n.factorial : ℝ) * ‖p n‖ ^ 2)) :
    p.radius = ∞ := by
  apply p.radius_eq_top_of_summable_norm
  intro r
  have hclock : Summable (fun n : ℕ => (r : ℝ) ^ (2 * n) / n.factorial) := by
    simpa only [pow_mul] using Real.summable_pow_div_factorial ((r : ℝ) ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (henergy.add hclock)
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hsq :
      (‖p n‖ * (r : ℝ) ^ n) ^ 2 =
        ((n.factorial : ℝ) * ‖p n‖ ^ 2) *
          ((r : ℝ) ^ (2 * n) / n.factorial) := by
    field_simp
    ring
  have htwo := two_mul_le_add_of_sq_le_mul
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (div_nonneg (by positivity) hfac.le) hsq.le
  nlinarith [mul_nonneg (norm_nonneg (p n))
    (by positivity : 0 ≤ (r : ℝ) ^ n)]

/-- Uniform boundedness of every finite factorial Fock energy is the cofinal interface needed by
the infinite-radius law; no separate infinite-series hypothesis is required. -/
theorem radius_eq_top_of_factorialFockPartialEnergy_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F) {C : ℝ}
    (henergy : ∀ N, ∑ n ∈ Finset.range N,
      (n.factorial : ℝ) * ‖p n‖ ^ 2 ≤ C) :
    p.radius = ∞ := by
  apply radius_eq_top_of_summable_factorialFockEnergy p
  exact summable_of_sum_range_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) henergy

/-- Summable raw-derivative factorial Fock energy forces the normalized formal Taylor series to
have infinite radius.  No analyticity hypothesis is needed for this coefficient-growth statement. -/
theorem radius_taylorSeries_eq_top_of_summable_rawJetFactorialFockEnergy
    (f : ℂ → ℂ) (a : ℂ)
    (henergy : Summable (fun n : ℕ =>
      ‖iteratedDeriv n f a‖ ^ 2 / n.factorial)) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n =>
      iteratedDeriv n f a / (n.factorial : ℂ))).radius = ∞ := by
  apply radius_eq_top_of_summable_factorialFockEnergy
  refine henergy.congr (fun n => ?_)
  rw [FormalMultilinearSeries.ofScalars_norm, norm_div,
    Complex.norm_natCast]
  field_simp

/-- **Cofinal raw-jet/Fock law.**  A single bound for every finite raw-jet factorial energy forces
the normalized formal Taylor series at that point to have infinite radius. -/
theorem radius_taylorSeries_eq_top_of_rawJetFactorialFockPartialEnergy_le
    (f : ℂ → ℂ) (a : ℂ) {C : ℝ}
    (henergy : ∀ N, ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n f a‖ ^ 2 / n.factorial ≤ C) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n =>
      iteratedDeriv n f a / (n.factorial : ℂ))).radius = ∞ := by
  apply radius_taylorSeries_eq_top_of_summable_rawJetFactorialFockEnergy
  exact summable_of_sum_range_le
    (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) henergy

/-- **Vector-valued factorial-Fock entire-extension law.**  An analytic germ whose finite raw-jet
factorial energies have one cofinal bound agrees near its base point with an entire function.  This
is the precise analytic-continuation conclusion behind factorial-clock pole obstructions; all
source-specific work is confined to proving the energy bound and exhibiting the incompatible
boundary obstruction. -/
theorem exists_entire_extension_of_rawJetFactorialFockPartialEnergy_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {a : ℂ} (hf : AnalyticAt ℂ f a) {C : ℝ}
    (henergy : ∀ N, ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n f a‖ ^ 2 / n.factorial ≤ C) :
    ∃ g : ℂ → E, AnalyticOnNhd ℂ g Set.univ ∧
      Filter.EventuallyEq (nhds a) f g := by
  obtain ⟨p, hpAt⟩ := hf
  have hpEnergy : ∀ N, ∑ n ∈ Finset.range N,
      (n.factorial : ℝ) * ‖p n‖ ^ 2 ≤ C := by
    intro N
    calc
      ∑ n ∈ Finset.range N, (n.factorial : ℝ) * ‖p n‖ ^ 2 =
          ∑ n ∈ Finset.range N,
            ‖iteratedDeriv n f a‖ ^ 2 / n.factorial := by
        apply Finset.sum_congr rfl
        intro n _
        obtain ⟨r, hr⟩ := hpAt
        have hfac := hr.factorial_smul (1 : ℂ) n
        rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
          Finset.prod_const_one, one_smul] at hfac
        change n.factorial • p.coeff n = iteratedDeriv n f a at hfac
        rw [← hfac, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul,
          FormalMultilinearSeries.norm_apply_eq_norm_coef]
        field_simp
      _ ≤ C := henergy N
  have hpRadius : p.radius = ∞ :=
    radius_eq_top_of_factorialFockPartialEnergy_le p hpEnergy
  have hpAnalytic : AnalyticOnNhd ℂ p.sum Set.univ := by
    have hp := p.analyticOnNhd
    rw [hpRadius] at hp
    simpa using hp
  refine ⟨fun z => p.sum (z - a), ?_, ?_⟩
  · intro z _
    have hinner : AnalyticAt ℂ (fun w : ℂ => w - a) z :=
      analyticAt_id.sub analyticAt_const
    exact AnalyticAt.fun_comp (f := fun w : ℂ => w - a) (x := z)
      (hpAnalytic (z - a) (Set.mem_univ _)) hinner
  · filter_upwards [hpAt.eventually_hasSum_sub] with z hz
    simpa only [FormalMultilinearSeries.sum] using hz.tsum_eq.symm

/-- **No-extension/Fock divergence interface.**  If an analytic germ has no entire continuation,
then its finite raw-jet factorial energies are unbounded.  This contrapositive exposes the exact
Prop a source-specific pole theorem must discharge. -/
theorem exists_rawJetFactorialFockPartialEnergy_gt_of_no_entire_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hno : ¬ ∃ g : ℂ → E, AnalyticOnNhd ℂ g Set.univ ∧
      Filter.EventuallyEq (nhds a) f g) (C : ℝ) :
    ∃ N, C < ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n f a‖ ^ 2 / n.factorial := by
  by_contra hbounded
  push Not at hbounded
  exact hno (exists_entire_extension_of_rawJetFactorialFockPartialEnergy_le
    hf hbounded)

end


end GaloisForLFunctions.HTGeometry
