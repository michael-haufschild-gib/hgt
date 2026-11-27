import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Tail

/-! # Sharp inverse error and attained separation for stationary reflection -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Filter Finset Real Set
open scoped Topology
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- Joint error in the value and moment-order slope of one Gibbs law. -/
def residual (p q : Nat.Primes) (d : ℝ) := max |reading p q d| |tangent p q d|

theorem residual_continuous (p q : Nat.Primes) : Continuous (residual p q) := by
  let E := spectrum p q
  have c (j : ℕ) : Continuous (variation E j) := continuous_iff_continuousAt.mpr
    fun x => (variation_deriv E j x).continuousAt
  have h := (c 0).abs.max (continuous_id.mul (c 1)).abs
  change Continuous (fun d => max |reading p q d| |tangent p q d|)
  simpa only [fun d => (readings p q d).1,fun d => (readings p q d).2,
    variation_zero_order,Pi.mul_def,id_eq] using h

theorem residual_even (p q : Nat.Primes) (d : ℝ) : residual p q (-d)=residual p q d := by
  let E := spectrum p q
  have odd : oddTrace E (-d)= -oddTrace E d := by
    simp only [oddTrace,oddTerm,neg_neg,←sum_neg_distrib,neg_sub]
  have even : variation E 1 (-d)=variation E 1 d := by
    unfold variation
    apply sum_congr rfl
    intro i _
    simp only [pow_one,neg_mul,mul_neg,neg_neg]
    ring
  simp only [residual,fun t => (readings p q t).1,fun t => (readings p q t).2]
  change max |oddTrace E (-d)| |(-d)*variation E 1 (-d)|=_
  rw [odd,even,neg_mul,abs_neg,abs_neg]

theorem residual_zero (p q : Nat.Primes) (d : ℝ) : residual p q d=0 ↔ d=0 := by
  constructor
  · intro hz
    let s : ℂ := (((d+1)/2 : ℝ) : ℂ)
    have damp : 2*s.re-1=d := by change 2*((d+1)/2)-1=d; ring
    let P := finiteGibbsStateWeight d (primeModes q (packet p))
    have value : lawDefect P 1=0 := abs_nonpos_iff.mp ((le_max_left _ _).trans_eq hz)
    have flat : deriv (lawDefect P) 1=0 := abs_nonpos_iff.mp ((le_max_right _ _).trans_eq hz)
    have h := stationary_isometry p q s
    dsimp only at h
    rw [damp,split_isometric_iff] at h
    have eq := h.mp ⟨(agrees_odd _ _).mpr value,flat ▸ (defect_derivative P).differentiableAt.hasDerivAt⟩
    change (d+1)/2=1/2 at eq
    linarith only [eq]
  · rintro rfl
    simp only [residual,(readings p q 0).1,(readings p q 0).2,odd_zero,zero_mul,abs_zero,max_self]

/-- The max-norm error has a nonzero cubic coefficient, giving the sharp
scale for either a measured residual or an upper bound on both readings. -/
theorem residual_limit (p q : Nat.Primes) :
    Tendsto (fun d => residual p q d/|d|^3) (𝓝[≠] 0) (𝓝 (3*cubic p q)) := by
  obtain ⟨v,s⟩ := cubic_readings p q
  have hc := cubic_pos p q
  have top : max (cubic p q) (3*cubic p q)=3*cubic p q := max_eq_right (by linarith only [hc])
  have divide (d a b : ℝ) : max (a/|d|^3) (b/|d|^3)=max a b/|d|^3 :=
    max_div_div_right (pow_nonneg (abs_nonneg d) 3) a b
  simpa only [abs_div,abs_pow,abs_of_pos hc,abs_of_pos (show 0<3*cubic p q by positivity),
    top,divide,residual] using v.abs.max s.abs

/-- A nonzero error away from the line has an attained, positive lower
bound on the full exterior, even across the false returns of the value alone. -/
theorem exterior_minimum (p q : Nat.Primes) (δ : ℝ) (hδ : 0<δ) :
    ∃ b : ℝ, δ≤b ∧ 0<residual p q b ∧ ∀ d : ℝ, δ≤|d| → residual p q b≤residual p q d := by
  let R := residual p q
  have grow := (reading_unbounded p q).eventually_ge_atTop (R δ)
  obtain ⟨M,hM⟩ := eventually_atTop.mp grow
  let B := max δ M
  have inside : δ≤B := le_max_left _ _
  obtain ⟨b,hb,minimal⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr inside)
    (residual_continuous p q).continuousOn
  have pos : 0<R b := lt_of_le_of_ne ((abs_nonneg _).trans (le_max_left _ _))
    (Ne.symm fun hz => (hδ.trans_le hb.1).ne' ((residual_zero p q b).mp hz))
  refine ⟨b,hb.1,pos,fun d hd => ?_⟩
  have minδ : R b≤R δ := minimal ⟨le_rfl,inside⟩
  have habs : R |d|=R d := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]; exact residual_even p q d
  change R b≤R d
  rw [←habs]
  by_cases h : |d|≤B
  · exact minimal ⟨hd,h⟩
  · have far : M≤|d| := (le_max_right δ M).trans (le_of_not_ge h)
    exact minδ.trans ((hM |d| far).trans (le_max_left _ _))

#print axioms residual_continuous
#print axioms residual_even
#print axioms residual_zero
#print axioms residual_limit
#print axioms exterior_minimum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution
