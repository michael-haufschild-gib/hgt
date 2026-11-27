import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Angular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Uniform sensitivity of real quadratures near a unitary character -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers

open Finset Real Filter Set
open scoped Topology

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The amplification relative to one elementary radial displacement,
with occupation normalization removing the elementary slope k. -/
def amplification (k : ℕ+) (x : ℝ) :=
  |sinh ((k : ℝ)*x)| / ((k : ℝ)*|sinh x|)

def sensitivity (k : I → ℕ+) (x y : ℝ) :=
  peak fun i => amplification (k i) x * |cos ((k i : ℝ)*y)|

private theorem sinh_multiple (n : ℕ) {t : ℝ} (ht : 0≤t) :
    (n : ℝ)*sinh t ≤ sinh ((n : ℝ)*t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := sinh_nonneg_iff.mpr ht
    have ha : 0≤sinh ((n : ℝ)*t) := sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) ht)
    have a := mul_le_mul_of_nonneg_left (one_le_cosh t) ha
    have b := mul_le_mul_of_nonneg_right (one_le_cosh ((n : ℝ)*t)) hs
    rw [Nat.cast_succ,add_mul,one_mul,add_mul,one_mul,sinh_add]
    linarith only [ih,a,b]

theorem amplification_ge_one (k : ℕ+) {x : ℝ} (hx : x≠0) : 1 ≤ amplification k x := by
  have hp : 0<(k : ℝ) := Nat.cast_pos.mpr k.pos
  apply (le_div_iff₀ (mul_pos hp (abs_pos.mpr (sinh_ne_zero.mpr hx)))).mpr
  simpa only [one_mul,abs_sinh,abs_mul,abs_of_pos hp] using
    (show (k : ℝ)*|sinh x|≤|sinh ((k : ℝ)*x)| by
      simpa only [abs_sinh,abs_mul,abs_of_pos hp] using sinh_multiple k.val (abs_nonneg x))

/-- For every finite occupation the normalized hyperbolic amplification
tends to one, from either side of the isometry line. -/
theorem amplification_limit (k : ℕ+) :
    Tendsto (amplification k) (𝓝[≠] 0) (𝓝 1) := by
  have slope (a : ℝ) : Tendsto (fun x : ℝ => sinh (a*x)/x) (𝓝[≠] 0) (𝓝 a) := by
    have lin : HasDerivAt (fun x : ℝ => a*x) a 0 := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul a
    simpa only [zero_add,mul_zero,sinh_zero,sub_zero,cosh_zero,one_mul,smul_eq_mul,
      div_eq_inv_mul] using lin.sinh.tendsto_slope_zero
  have hp : 0<(k : ℝ) := Nat.cast_pos.mpr k.pos
  have top := (slope (k : ℝ)).abs
  have bot := (slope 1).abs.const_mul (k : ℝ)
  simp only [one_mul,abs_one,mul_one] at bot
  have quotient := top.div bot hp.ne'
  rw [abs_of_pos hp,div_self hp.ne'] at quotient
  apply quotient.congr'
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[≠] 0, x≠0 from self_mem_nhdsWithin] with x hx
  change |sinh ((k : ℝ)*x)/x| / ((k : ℝ)*|sinh x/x|)=_
  rw [abs_div,abs_div,amplification]
  field_simp

theorem sensitivity_lower (k : I → ℕ+) (x y : ℝ) (hx : x≠0) :
    gain k ≤ sensitivity k x y := by
  obtain ⟨i,eq⟩ := peak_value (fun j => |cos ((k j : ℝ)*y)|)
  have lower := gain_le k y
  change gain k ≤ peak _ at lower
  rw [eq] at lower
  exact lower.trans ((le_mul_of_one_le_left (abs_nonneg _) (amplification_ge_one _ hx)).trans
    (to_peak (fun j => amplification (k j) x * |cos ((k j : ℝ)*y)|) i))

/-- Finite maximization commutes with pointwise convergence, including
along a punctured filter. -/
theorem peak_limit {A : Type*} {l : Filter A} (f : A → I → ℝ) (b : I → ℝ)
    (each : ∀ i, Tendsto (fun x => f x i) l (𝓝 (b i))) :
    Tendsto (fun x => peak (f x)) l (𝓝 (peak b)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨i,eq⟩ := peak_value b
    have lo := (each i).eventually_const_lt (ha.trans_eq eq)
    exact lo.mono fun x hx => hx.trans_le (to_peak (f x) i)
  · intro a ha
    have upper : ∀ᶠ x in l, ∀ i, f x i<a :=
      eventually_all.mpr fun i => (each i).eventually_lt_const ((to_peak b i).trans_lt ha)
    filter_upwards [upper] with x hx
    obtain ⟨i,eq⟩ := peak_value (f x)
    exact eq.trans_lt (hx i)

theorem sensitivity_limit (k : I → ℕ+) (y : ℝ) :
    Tendsto (fun x => sensitivity k x y) (𝓝[≠] 0) (𝓝 (angular k y)) := by
  apply peak_limit
  intro i
  simpa only [one_mul] using (amplification_limit (k i)).mul_const |cos ((k i : ℝ)*y)|

/-- The same sharp constant holds on every punctured neighborhood,
with an explicit finite formula, even when some phases are exactly blind. -/
theorem sharp_local_gain (k : I → ℕ+) (δ : ℝ) (hδ : 0<δ) (K : ℝ) :
    (∀ x y : ℝ, x≠0 → |x|<δ → K≤sensitivity k x y) ↔ K≤gain k := by
  constructor
  · intro h
    obtain ⟨y,hit⟩ := attain_gain k
    have small : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x|<δ := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact continuous_abs.continuousAt.tendsto.eventually_lt_const (by simpa only [abs_zero] using hδ)
    have near : ∀ᶠ x : ℝ in 𝓝[≠] 0, K≤sensitivity k x y := by
      filter_upwards [small,show ∀ᶠ x : ℝ in 𝓝[≠] 0, x≠0 from self_mem_nhdsWithin] with x hs hx
      exact h x y hx hs
    exact (le_of_tendsto_of_tendsto tendsto_const_nhds (sensitivity_limit k y) near).trans_eq hit
  · exact fun h x y hx _ => h.trans (sensitivity_lower k x y hx)

#print axioms amplification_ge_one
#print axioms amplification_limit
#print axioms sensitivity_lower
#print axioms peak_limit
#print axioms sensitivity_limit
#print axioms sharp_local_gain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers
