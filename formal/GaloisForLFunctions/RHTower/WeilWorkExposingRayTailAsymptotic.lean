import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality
import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity

/-!
# Sign and sharp exponential rate of the literal exposing ray

The actual exposing coefficients are eventually positive and satisfy
`log (exposingWeight n) / n → -2 * π * exp (-2)`.
The existing box tail is strictly positive at every finite cutoff and decays at
all exponential rates below this endpoint.

The theta autocorrelation has sharp two-sided double-exponential envelopes.
In the literal polar second difference, the outermost positive shift has size two,
while every negative shift has size at most one. Summability of the mixture makes
this separation survive the infinite sum without assuming positivity of its terms.

These are unconditional source-tail results. They sharpen the repair budget;
the universal matched-family energy lower bound remains open.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/TAIL-SIGN-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real
noncomputable section
namespace RHTower
namespace ExposingRayTail

/-- Pointwise double-exponential lower envelope for the literal theta kernel. -/
theorem phi_lower (x : ℝ) :
    2 * π ^ 2 * exp (-(π * exp (2 * |x|))) ≤ riemannKernelReal x := by
  have h := (riemannLeadTerm_ge (abs_nonneg x)).trans (riemannKernelReal_sandwich x).1
  have h1 : 1 ≤ exp (2 * |x|) ^ 2 := one_le_pow₀ (Real.one_le_exp (by positivity))
  have h2 : 1 ≤ exp (|x| / 2) := Real.one_le_exp (by positivity)
  have hp : 0 < exp (-(π * exp (2 * |x|))) := exp_pos _
  have hπ := Real.pi_pos
  have h3 := one_le_mul_of_one_le_of_one_le h1 h2
  have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2*π^2*exp (-(π*exp (2*|x|))) by positivity)
  rw [neg_mul] at h
  nlinarith

private theorem phi_upper {c : ℝ} (hc : 0 < c) (hcπ : c < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, riemannKernelReal x ≤
      B * exp (-(c * exp (2 * |x|))) * exp (-|x|) := by
  let d := π - c
  have hd : 0 < d := by dsimp [d]; linarith
  let B := (101 / 100 : ℝ) * (4 * π ^ 2) * (6 / d ^ 3)
  refine ⟨B, by dsimp [B]; positivity, fun x => ?_⟩
  let u := |x|
  let X := exp (2 * u)
  have hu : 0 ≤ u := abs_nonneg x
  have hX : 0 < X := exp_pos _
  have hlead : riemannLeadTerm u ≤ 4 * π ^ 2 * exp (9 * u / 2) * exp (-(π * X)) := by
    unfold riemannLeadTerm
    have hp : 4 * π ^ 2 * exp (2 * u) - 6 * π ≤ 4 * π ^ 2 * exp (2 * u) := by
      linarith [Real.pi_pos]
    calc _ ≤ exp (5 * u / 2) * (4 * π ^ 2 * exp (2 * u)) * exp (-π * exp (2 * u)) := by gcongr
      _ = _ := by dsimp [X]; rw [show exp (5*u/2) * (4*π^2*exp (2*u)) =
          4*π^2*(exp (5*u/2)*exp (2*u)) by ring, ← exp_add]; congr 3 <;> ring
  have he : exp (9 * u / 2) ≤ X ^ 3 * exp (-u) := by
    dsimp [X]
    rw [← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr; norm_num; linarith
  have ht := Real.pow_div_factorial_le_exp (x := d * X) (by positivity) 3
  norm_num [Nat.factorial] at ht
  have hpay : X ^ 3 * exp (-(d * X)) ≤ 6 / d ^ 3 := by
    have hx := exp_pos (-(d*X))
    have heq : exp (d*X) * exp (-(d*X)) = 1 := by rw [← exp_add]; simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pow d X 3]
  calc riemannKernelReal x ≤ (101/100) * riemannLeadTerm u := (riemannKernelReal_sandwich x).2
    _ ≤ (101/100) * (4 * π ^ 2 * exp (9*u/2) * exp (-(π*X))) := by gcongr
    _ ≤ (101/100) * (4 * π ^ 2 * (X^3*exp (-u)) * exp (-(π*X))) := by gcongr
    _ = (101/100) * (4*π^2) * (X^3*exp (-(d*X))) * exp (-(c*X)) * exp (-u) := by
      have heq : exp (-(π*X)) = exp (-(d*X)) * exp (-(c*X)) := by
        rw [← exp_add]; congr 1; dsimp [d]; ring
      rw [heq]; ring
    _ ≤ (101/100) * (4*π^2) * (6/d^3) * exp (-(c*X)) * exp (-u) := by gcongr
    _ = _ := rfl

private theorem corr_integrable (y : ℝ) :
    Integrable (fun t => riemannKernelReal t * riemannKernelReal (t - y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  apply integrable_riemannKernel_mul_shift continuous_riemannKernelReal hC0
    (fun t => ?_) y
  rw [abs_of_pos (riemannKernelReal_pos _)]
  exact (hC t).trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
    linarith [abs_nonneg t])) hC0)

/-- Sharp subcritical theta envelope for the actual autocorrelation. -/
theorem autocorr_upper {c : ℝ} (hc : 0 < c) (hcπ : c < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, riemannKernelAutocorr y ≤ C * exp (-(2 * c * exp |y|)) := by
  obtain ⟨B, hB, hPhi⟩ := phi_upper hc hcπ
  refine ⟨2 * B ^ 2, by positivity, fun y => ?_⟩
  have hpoint : ∀ t : ℝ, riemannKernelReal t * riemannKernelReal (t - y) ≤
      (B ^ 2 * exp (-(2 * c * exp |y|))) * exp (-|t|) := by
    intro t
    have hsum : 2 * exp |y| ≤ exp (2 * |t|) + exp (2 * |t - y|) := by
      have htri : |y| ≤ |t| + |t - y| := calc
        |y| = |t - (t-y)| := by congr 1; ring
        _ ≤ |t| + |t-y| := abs_sub _ _
      have hexp := exp_le_exp.mpr htri
      rw [exp_add] at hexp
      have he1 : exp (2 * |t|) = exp |t| ^ 2 := by rw [show 2 * |t| = |t| + |t| by ring, exp_add, sq]
      have he2 : exp (2 * |t - y|) = exp |t - y| ^ 2 := by
        rw [show 2 * |t - y| = |t - y| + |t - y| by ring, exp_add, sq]
      rw [he1, he2]
      nlinarith [sq_nonneg (exp |t| - exp |t - y|)]
    have he : exp (-(c * exp (2 * |t|))) * exp (-(c * exp (2 * |t - y|))) ≤
        exp (-(2 * c * exp |y|)) := by
      rw [← exp_add]; apply exp_le_exp.mpr; nlinarith
    have hsmall : exp (-|t - y|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (t-y)])
    calc _ ≤ (B * exp (-(c * exp (2 * |t|))) * exp (-|t|)) *
          (B * exp (-(c * exp (2 * |t-y|))) * exp (-|t-y|)) :=
        mul_le_mul (hPhi t) (hPhi (t-y)) (riemannKernelReal_pos _).le (by positivity)
      _ = B ^ 2 * (exp (-(c * exp (2 * |t|))) * exp (-(c * exp (2 * |t-y|)))) *
          exp (-|t|) * exp (-|t-y|) := by ring
      _ ≤ B ^ 2 * exp (-(2 * c * exp |y|)) * exp (-|t|) * 1 := by gcongr
      _ = _ := by ring
  have hi := integral_mono (corr_integrable y)
    (integrable_exp_neg_abs.const_mul (B ^ 2 * exp (-(2 * c * exp |y|)))) hpoint
  rw [integral_const_mul, integral_exp_neg_abs] at hi
  change (∫ t, riemannKernelReal t * riemannKernelReal (t-y)) ≤ _
  nlinarith

/-- Every supercritical theta rate is a lower envelope on the positive tail. -/
theorem autocorr_lower {b : ℝ} (hb : 2 * π < b) :
    ∃ D Y : ℝ, 0 < D ∧ ∀ y, Y ≤ y →
      D * exp (-(b * exp y)) ≤ riemannKernelAutocorr y := by
  have hb0 : 0 < b := lt_trans (by positivity) hb
  let δ := log (b / (2 * π)) / 2
  have hδ : 0 < δ := by
    dsimp [δ]; apply div_pos (Real.log_pos ?_) (by norm_num)
    exact (one_lt_div (by positivity)).mpr hb
  have heδ : exp (2 * δ) = b / (2 * π) := by
    dsimp [δ]; rw [show 2 * (log (b / (2 * π)) / 2) = log (b / (2 * π)) by ring,
      exp_log (by positivity)]
  refine ⟨2 * δ * (2 * π ^ 2) ^ 2, 2 * δ, by positivity, fun y hy => ?_⟩
  have hpoint : ∀ t ∈ Ioc (y / 2 - δ) (y / 2 + δ),
      (2 * π ^ 2) ^ 2 * exp (-(b * exp y)) ≤ riemannKernelReal t * riemannKernelReal (t-y) := by
    intro t ht
    have ht1 : |t| ≤ y/2+δ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have ht2 : |t-y| ≤ y/2+δ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hs : π * (exp (2 * |t|) + exp (2 * |t-y|)) ≤ b * exp y := by
      have h1 := exp_le_exp.mpr (show 2 * |t| ≤ y + 2 * δ by linarith)
      have h2 := exp_le_exp.mpr (show 2 * |t-y| ≤ y + 2 * δ by linarith)
      rw [exp_add, heδ] at h1 h2
      have hπ := Real.pi_pos
      have he : 2 * π * (exp y * (b / (2 * π))) = b * exp y := by field_simp
      nlinarith
    have heq (U V : ℝ) : (2*π^2*exp U)*(2*π^2*exp V) =
        (2*π^2)^2*exp (U+V) := by rw [exp_add]; ring
    have hprod : (2*π^2)^2*exp (-(b*exp y)) ≤
        (2*π^2*exp (-(π*exp (2*|t|))))*(2*π^2*exp (-(π*exp (2*|t-y|)))) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply exp_le_exp.mpr
      linarith
    exact hprod.trans (mul_le_mul (phi_lower t) (phi_lower (t-y)) (by positivity)
      (riemannKernelReal_pos _).le)
  have hi := setIntegral_mono_on (integrableOn_const (by simp))
    (corr_integrable y).integrableOn measurableSet_Ioc hpoint
  have hconst : (∫ t in Ioc (y/2-δ) (y/2+δ), (2 * π ^ 2) ^ 2 * exp (-(b * exp y))) =
      (2 * δ * (2 * π ^ 2) ^ 2) * exp (-(b * exp y)) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]; ring
  rw [hconst] at hi
  exact hi.trans (setIntegral_le_integral (corr_integrable y)
    (Eventually.of_forall fun t => mul_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le))


private theorem polar_expand (c y : ℝ) :
    polarExposingKernel c y =
      (1 + 2 * polarWeight c ^ 2) * riemannKernelAutocorr y -
      2 * polarWeight c * (riemannKernelAutocorr (y-c) + riemannKernelAutocorr (y+c)) +
      polarWeight c ^ 2 * (riemannKernelAutocorr (y-2*c) + riemannKernelAutocorr (y+2*c)) := by
  unfold polarExposingKernel polarShift
  rw [show y-c-c = y-2*c by ring, show y-c+c = y by ring,
    show y+c-c = y by ring, show y+c+c = y+2*c by ring]
  ring

private theorem shifted_upper {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hK : ∀ y, riemannKernelAutocorr y ≤ C * exp (-(2*a*exp |y|)))
    (y r s : ℝ) (hs : |s| ≤ r) :
    riemannKernelAutocorr (y+s) ≤ C * exp (-(2*a*exp (|y|-r))) := by
  refine (hK (y+s)).trans ?_
  have ht := abs_sub_abs_le_abs_sub y (y+s)
  rw [show y-(y+s) = -s by ring, abs_neg] at ht
  have he : exp (|y|-r) ≤ exp |y+s| := exp_le_exp.mpr (by linarith)
  gcongr

private theorem polar_bounds {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hK : ∀ y, riemannKernelAutocorr y ≤ C * exp (-(2*a*exp |y|)))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (y : ℝ) :
    |polarExposingKernel c y| ≤ 2*C*exp (-(2*a*exp (|y|-2))) ∧
    polarWeight c ^ 2 * riemannKernelAutocorr (y-2*c) -
      2*C*exp (-(2*a*exp (|y|-1))) ≤ polarExposingKernel c y := by
  let p := polarWeight c
  have hp : 0 < p := polarWeight_pos c
  have hp1 : p ≤ 1/2 := polarWeight_le_half c
  have hp2 : p^2 ≤ 1/4 := by nlinarith
  let H := C*exp (-(2*a*exp (|y|-2)))
  let J := C*exp (-(2*a*exp (|y|-1)))
  have hH : 0 < H := by dsimp [H]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hb (s : ℝ) (hs : |s| ≤ 2) : riemannKernelAutocorr (y+s) ≤ H :=
    shifted_upper ha hC hK y 2 s hs
  have hj (s : ℝ) (hs : |s| ≤ 1) : riemannKernelAutocorr (y+s) ≤ J :=
    shifted_upper ha hC hK y 1 s hs
  have h0 : riemannKernelAutocorr y ≤ H := by simpa using hb 0 (by norm_num)
  have hm2 : riemannKernelAutocorr (y-2*c) ≤ H := by
    simpa [sub_eq_add_neg] using hb (-(2*c)) (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith)
  have hp2k : riemannKernelAutocorr (y+2*c) ≤ H :=
    hb (2*c) (by rw [abs_of_nonneg (by positivity)]; linarith)
  have hm : riemannKernelAutocorr (y-c) ≤ J := by
    simpa [sub_eq_add_neg] using hj (-c) (by rw [abs_neg, abs_of_nonneg hc0]; exact hc1)
  have hpk : riemannKernelAutocorr (y+c) ≤ J := hj c (by rwa [abs_of_nonneg hc0])
  have hA : (1+2*p^2)*riemannKernelAutocorr y +
      p^2*(riemannKernelAutocorr (y-2*c)+riemannKernelAutocorr (y+2*c)) ≤ 2*H := by
    calc _ ≤ (1+2*p^2)*H + p^2*(H+H) := by gcongr
      _ ≤ 2*H := by nlinarith
  have hB : 2*p*(riemannKernelAutocorr (y-c)+riemannKernelAutocorr (y+c)) ≤ 2*J := by
    calc _ ≤ 2*p*(J+J) := by gcongr
      _ ≤ 2*J := by nlinarith
  have hJH : J ≤ H := by dsimp [J,H]; gcongr; linarith
  have hB0 : 0 ≤ 2*p*(riemannKernelAutocorr (y-c)+riemannKernelAutocorr (y+c)) := by
    have := riemannKernelAutocorr_pos (y-c); have := riemannKernelAutocorr_pos (y+c); positivity
  have hA0 : 0 ≤ (1+2*p^2)*riemannKernelAutocorr y := by
    have := riemannKernelAutocorr_pos y; positivity
  have hplus : 0 ≤ p^2*riemannKernelAutocorr (y+2*c) :=
    mul_nonneg (sq_nonneg _) (riemannKernelAutocorr_pos _).le
  have hminus : 0 ≤ p^2*riemannKernelAutocorr (y-2*c) :=
    mul_nonneg (sq_nonneg _) (riemannKernelAutocorr_pos _).le
  rw [polar_expand]
  dsimp [p,H,J] at *
  constructor
  · exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · nlinarith

private theorem log_exp_shift {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    exp (|log n|-r) = exp (-r) * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_of_nonneg (Real.log_nonneg hnR), sub_eq_add_neg, exp_add,
    exp_log (by positivity)]
  ring

/-- Every subcritical exponential rate bounds the entire literal exposing sequence. -/
theorem weight_upper {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |exposingWeight n| ≤ C * exp (-(2*a*exp (-2)*(n:ℝ))) := by
  obtain ⟨C, hC, hK⟩ := autocorr_upper ha haπ
  refine ⟨8*C, by positivity, fun n hn => ?_⟩
  let H := C*exp (-(2*a*exp (|log n|-2)))
  have hb (k : ℕ) (y : ℝ) : |polarExposingKernel (1/((k:ℝ)+1)) y| ≤
      2*C*exp (-(2*a*exp (|y|-2))) :=
    (polar_bounds ha hC hK (by positivity) (by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]) y).1
  have hterm (k : ℕ) : ‖(1/2:ℝ)^k *
      (polarExposingKernel (1/((k:ℝ)+1)) (log n) +
       polarExposingKernel (1/((k:ℝ)+1)) (-log n))‖ ≤ (1/2:ℝ)^k * (4*H) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp := hb k (log n)
    have hm := hb k (-log n)
    rw [abs_neg] at hm
    have hs := abs_add_le (polarExposingKernel (1/((k:ℝ)+1)) (log n))
      (polarExposingKernel (1/((k:ℝ)+1)) (-log n))
    dsimp [H]; linarith
  have ht := tsum_of_norm_bounded (hasSum_geometric_two.mul_right (4*H)) hterm
  change |exposingWeight n| ≤ _
  rw [Real.norm_eq_abs] at ht
  change |exposingWeight n| ≤ 2*(4*H) at ht
  dsimp [H] at ht
  rw [log_exp_shift hn 2] at ht
  convert ht using 1; ring_nf

private theorem weight_lower_split {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hK : ∀ y, riemannKernelAutocorr y ≤ C*exp (-(2*a*exp |y|)))
    {n : ℕ} (hn : 1 ≤ n) :
    polarWeight 1 ^ 2 * riemannKernelAutocorr (log n-2) -
      8*C*exp (-(2*a*exp (-1)*(n:ℝ))) ≤ exposingWeight n := by
  let y := log (n:ℝ)
  let H := C*exp (-(2*a*exp (|y|-1)))
  let f (k : ℕ) := (1/2:ℝ)^k *
    (polarExposingKernel (1/((k:ℝ)+1)) y + polarExposingKernel (1/((k:ℝ)+1)) (-y))
  have hs : Summable f := summable_exposingWeight_term n
  have hH : 0 < H := by dsimp [H]; positivity
  have hpair (k : ℕ) : polarWeight (1/((k:ℝ)+1)) ^ 2 *
      riemannKernelAutocorr (y-2*(1/((k:ℝ)+1))) - 4*H ≤
      polarExposingKernel (1/((k:ℝ)+1)) y + polarExposingKernel (1/((k:ℝ)+1)) (-y) := by
    have hc1 : 1/((k:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hp := (polar_bounds ha hC hK (by positivity) hc1 y).2
    have hm := (polar_bounds ha hC hK (by positivity) hc1 (-y)).2
    rw [abs_neg] at hm
    have h0 : 0 ≤ polarWeight (1/((k:ℝ)+1)) ^ 2 *
        riemannKernelAutocorr (-y-2*(1/((k:ℝ)+1))) :=
      mul_nonneg (sq_nonneg _) (riemannKernelAutocorr_pos _).le
    dsimp [H]; linarith
  have hnneg (k : ℕ) : 0 ≤ f k + (1/2:ℝ)^k * (4*H) := by
    have hp := hpair k
    have h0 : 0 ≤ polarWeight (1/((k:ℝ)+1)) ^ 2 *
        riemannKernelAutocorr (y-2*(1/((k:ℝ)+1))) :=
      mul_nonneg (sq_nonneg _) (riemannKernelAutocorr_pos _).le
    have hb0 : -(4*H) ≤ polarExposingKernel (1/((k:ℝ)+1)) y +
        polarExposingKernel (1/((k:ℝ)+1)) (-y) := by linarith
    have hm := mul_le_mul_of_nonneg_left hb0 (by positivity : 0 ≤ (1/2:ℝ)^k)
    dsimp [f]; nlinarith
  have hs2 := summable_geometric_two.mul_right (4*H)
  have ht := (hs.add hs2).le_tsum 0 (fun k _ => hnneg k)
  rw [hs.tsum_add hs2, tsum_mul_right, hasSum_geometric_two.tsum_eq] at ht
  have hp := hpair 0
  norm_num at hp
  have hf0 : f 0 = polarExposingKernel 1 y + polarExposingKernel 1 (-y) := by simp [f]
  rw [hf0] at ht
  change polarExposingKernel 1 y + polarExposingKernel 1 (-y) + (1/2:ℝ)^0*(4*H) ≤
    exposingWeight n + 2*(4*H) at ht
  norm_num at ht
  have hfin : polarWeight 1 ^ 2 * riemannKernelAutocorr (y-2) - 8*H ≤ exposingWeight n := by linarith
  dsimp [H,y] at hfin
  rw [log_exp_shift hn 1] at hfin
  convert hfin using 1; ring_nf


private theorem exponential_gap {a b P : ℝ} (hab : a < b) (hP : 0 < P) (Q : ℝ) :
    ∀ᶠ n : ℕ in atTop, Q * exp (-(b*n)) ≤ P * exp (-(a*n)) := by
  let q := exp (-(b-a))
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul Q
  have he : ∀ᶠ n : ℕ in atTop, Q*q^n < P := ht.eventually_lt_const (by simpa using hP)
  filter_upwards [he] with n hn
  have heq : Q * exp (-(b*n)) = (Q*q^n) * exp (-(a*n)) := by
    dsimp [q]
    rw [← exp_nat_mul, mul_assoc, ← exp_add]
    congr 2; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hn.le (exp_pos _).le

private theorem eventually_log_nat_ge (Y : ℝ) : ∀ᶠ n : ℕ in atTop, Y ≤ log n - 2 := by
  refine eventually_atTop.2 ⟨⌈exp (Y+2)⌉₊, fun n hn => ?_⟩
  have hnR : exp (Y+2) ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hlog := Real.log_le_log (exp_pos (Y+2)) hnR
  rw [log_exp] at hlog
  linarith

end ExposingRayTail

/-- The sharp integer-index exponential rate of the literal exposing ray. -/
def exposingWeightDecayRate : ℝ := 2*π*exp (-2)

theorem exposingWeightDecayRate_pos : 0 < exposingWeightDecayRate := by
  unfold exposingWeightDecayRate; positivity

/-- Every rate below the theta endpoint bounds the full exposing-weight sequence. -/
theorem exposingWeight_exponential_upper {r : ℝ} (hr : 0 < r) (hrr : r < exposingWeightDecayRate) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |exposingWeight n| ≤ C*exp (-(r*n)) := by
  let a := r / (2*exp (-2))
  have ha : 0 < a := by dsimp [a]; positivity
  have haπ : a < π := by
    dsimp [a]; rw [div_lt_iff₀ (by positivity)]
    unfold exposingWeightDecayRate at hrr
    nlinarith
  obtain ⟨C,hC,h⟩ := ExposingRayTail.weight_upper ha haπ
  refine ⟨C,hC,fun n hn => ?_⟩
  have heq : 2*a*exp (-2) = r := by dsimp [a]; field_simp
  simpa only [heq] using h n hn

/-- Every rate above the endpoint is eventually a positive lower envelope. -/
theorem exposingWeight_exponential_lower {r : ℝ} (hr : exposingWeightDecayRate < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, D*exp (-(r*n)) ≤ exposingWeight n := by
  let b := min (r / exp (-2)) (5*π/2)
  have hb : 2*π < b := by
    apply lt_min
    · rw [lt_div_iff₀ (exp_pos _)]
      exact hr
    · nlinarith [Real.pi_pos]
  have hbr : b*exp (-2) ≤ r := by
    have h := min_le_left (r / exp (-2)) (5*π/2)
    exact (le_div_iff₀ (exp_pos _)).mp h
  obtain ⟨D,Y,hD,hKlow⟩ := ExposingRayTail.autocorr_lower hb
  obtain ⟨C,hC,hKup⟩ := ExposingRayTail.autocorr_upper
    (c := 3*π/4) (by positivity) (by nlinarith [Real.pi_pos])
  let P := polarWeight 1 ^ 2 * D
  have hP : 0 < P := by dsimp [P]; exact mul_pos (sq_pos_of_pos (polarWeight_pos 1)) hD
  have hrate : b*exp (-2) < 2*(3*π/4)*exp (-1) := by
    have hb5 : b ≤ 5*π/2 := min_le_right _ _
    have he : exp (-1) = exp 1 * exp (-2) := by rw [← exp_add]; norm_num
    rw [he]
    have hh : b < 2*(3*π/4)*exp 1 := by nlinarith [Real.exp_one_gt_two, Real.pi_pos]
    nlinarith [mul_lt_mul_of_pos_right hh (exp_pos (-2))]
  have hgap := ExposingRayTail.exponential_gap hrate (show 0 < P/2 by positivity) (8*C)
  refine ⟨P/2, by positivity, ?_⟩
  filter_upwards [hgap, ExposingRayTail.eventually_log_nat_ge Y, eventually_ge_atTop (1:ℕ)] with n hn hny hn1
  have hexp : exp (log (n:ℝ)-2) = exp (-2)*(n:ℝ) := by
    rw [sub_eq_add_neg, exp_add, exp_log (by exact_mod_cast (show 0<n by omega))]; ring
  have hlow := hKlow (log (n:ℝ)-2) hny
  rw [hexp] at hlow
  have hsplit := ExposingRayTail.weight_lower_split (a := 3*π/4) (by positivity) hC hKup hn1
  have hmain : P*exp (-(b*exp (-2)*(n:ℝ))) -
      8*C*exp (-(2*(3*π/4)*exp (-1)*(n:ℝ))) ≤ exposingWeight n := by
    have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg (polarWeight 1))
    dsimp [P]
    have he : b*(exp (-2)*(n:ℝ)) = b*exp (-2)*(n:ℝ) := by ring
    rw [he] at hmul
    nlinarith
  have hsmall : exp (-(r*(n:ℝ))) ≤ exp (-(b*exp (-2)*(n:ℝ))) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ P/2 by positivity)
  nlinarith

/-- The exposing ray has a strictly positive tail, unconditionally. -/
theorem exposingWeight_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < exposingWeight n := by
  obtain ⟨D,hD,h⟩ := exposingWeight_exponential_lower
    (r := exposingWeightDecayRate+1) (by linarith)
  filter_upwards [h] with n hn
  exact (mul_pos hD (exp_pos _)).trans_le hn


/-- Exact logarithmic decay of the exposing coefficients, with their eventual positive sign. -/
theorem exposingWeight_log_decay :
    Tendsto (fun n : ℕ => log (exposingWeight n) / n) atTop (𝓝 (-exposingWeightDecayRate)) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    let r := (exposingWeightDecayRate-l)/2
    have hr : exposingWeightDecayRate < r := by dsimp [r]; linarith
    have hlr : l+r < 0 := by dsimp [r]; linarith
    obtain ⟨D,hD,hlo⟩ := exposingWeight_exponential_lower hr
    have he := (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (log D))).1 (l+r) hlr
    filter_upwards [hlo,he,eventually_ge_atTop (1:ℕ)] with n hn he hn1
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hw : 0 < exposingWeight n := (mul_pos hD (exp_pos _)).trans_le hn
    have hlog := Real.log_le_log (mul_pos hD (exp_pos (-(r*n)))) hn
    rw [Real.log_mul hD.ne' (exp_pos _).ne', log_exp] at hlog
    have he' := (lt_div_iff₀ hn0).mp he
    apply (lt_div_iff₀ hn0).mpr
    nlinarith
  · intro u hu
    let v := max 0 (-u)
    have hv : v < exposingWeightDecayRate := max_lt exposingWeightDecayRate_pos (by linarith)
    let r := (exposingWeightDecayRate+v)/2
    have hr0 : 0 < r := by dsimp [r]; have := le_max_left (0:ℝ) (-u); linarith [exposingWeightDecayRate_pos]
    have hr1 : r < exposingWeightDecayRate := by dsimp [r]; linarith
    have hur : 0 < u+r := by dsimp [r]; have := le_max_right (0:ℝ) (-u); dsimp [v] at hv ⊢; linarith
    obtain ⟨C,hC,hup⟩ := exposingWeight_exponential_upper hr0 hr1
    have he := (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (log C))).2 (u+r) hur
    filter_upwards [he,exposingWeight_eventually_pos,eventually_ge_atTop (1:ℕ)] with n he hw hn1
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hn := hup n hn1
    rw [abs_of_pos hw] at hn
    have hlog := Real.log_le_log hw hn
    rw [Real.log_mul hC.ne' (exp_pos _).ne', log_exp] at hlog
    have he' := (div_lt_iff₀ hn0).mp he
    apply (div_lt_iff₀ hn0).mpr
    nlinarith

private theorem exposingMajorant_exponential_upper {r : ℝ} (hr : 0 < r)
    (hrr : r < exposingWeightDecayRate) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, exposingMajorant n ≤ C*exp (-(r*n)) := by
  let s := (r+exposingWeightDecayRate)/2
  have hrs : r < s := by dsimp [s]; linarith
  have hs : s < exposingWeightDecayRate := by dsimp [s]; linarith
  obtain ⟨C,hC,hw⟩ := exposingWeight_exponential_upper (show 0<s by linarith) hs
  let d := s-r
  have hd : 0 < d := by dsimp [d]; linarith
  let B := C * (1/d + boxConst)
  have hB : 0 < B := by dsimp [B]; have := boxConst_nonneg; positivity
  refine ⟨B,hB,fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hl : log (n:ℝ) ≤ n := le_trans (Real.log_le_sub_one_of_pos hn0) (by linarith)
    have hx : (n:ℝ)*exp (-(d*n)) ≤ 1/d := by
      have he : d*(n:ℝ) ≤ exp (d*n) := le_trans (by linarith) (Real.add_one_le_exp _)
      have hm := mul_le_mul_of_nonneg_right he (exp_pos (-(d*n))).le
      have heq : exp (d*n)*exp (-(d*n)) = 1 := by rw [← exp_add]; simp
      rw [heq] at hm
      rw [le_div_iff₀ hd]
      nlinarith
    have hsmall : exp (-(d*n)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have hlog0 : 0 ≤ log (n:ℝ)+boxConst := by
      have := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega) : (1:ℝ)≤n)
      have := boxConst_nonneg
      linarith
    rw [exposingMajorant, if_pos hn]
    calc (log (n:ℝ)+boxConst)*|exposingWeight n| ≤
          (log (n:ℝ)+boxConst)*(C*exp (-(s*n))) :=
        mul_le_mul_of_nonneg_left (hw n (by omega)) hlog0
      _ ≤ ((n:ℝ)+boxConst)*(C*exp (-(s*n))) := by gcongr
      _ = C*((n:ℝ)*exp (-(d*n))+boxConst*exp (-(d*n)))*exp (-(r*n)) := by
        have heq : exp (-(s*n)) = exp (-(d*n))*exp (-(r*n)) := by
          rw [← exp_add]; congr 1; dsimp [d]; ring
        rw [heq]; ring
      _ ≤ C*(1/d+boxConst*1)*exp (-(r*n)) := by gcongr; exact boxConst_nonneg
      _ = B*exp (-(r*n)) := by dsimp [B]; ring
  · rw [exposingMajorant,if_neg hn]
    positivity

/-- The existing repair budget decays at every rate below the exact theta endpoint. -/
theorem exposingTail_exponential_upper {r : ℝ} (hr : 0 < r)
    (hrr : r < exposingWeightDecayRate) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, exposingTail N ≤ C*exp (-(r*N)) := by
  let s := (r+exposingWeightDecayRate)/2
  have hrs : r < s := by dsimp [s]; linarith
  have hs : s < exposingWeightDecayRate := by dsimp [s]; linarith
  obtain ⟨C,hC,hmaj⟩ := exposingMajorant_exponential_upper (show 0<s by linarith) hs
  let q := exp (-(s-r))
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  let B := C*(1-q)⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,fun N => ?_⟩
  have hterm (n : ℕ) : (if N<n then exposingMajorant n else 0) ≤
      (C*exp (-(r*N)))*q^n := by
    split_ifs with hn
    · have hnR : (N:ℝ) ≤ n := by exact_mod_cast hn.le
      have he : exp (-(r*n)) ≤ exp (-(r*N)) := exp_le_exp.mpr (by nlinarith)
      calc exposingMajorant n ≤ C*exp (-(s*n)) := hmaj n
        _ = C*exp (-(r*n))*q^n := by
          dsimp [q]; rw [← exp_nat_mul, mul_assoc, ← exp_add]; congr 2; ring
        _ ≤ _ := by gcongr
    · positivity
  have ht := (summable_exposingTail_terms N).tsum_le_tsum hterm
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (C*exp (-(r*N))))
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1] at ht
  change exposingTail N ≤ _ at ht
  dsimp [B]
  nlinarith

/-- No finite truncation exhausts the literal exposing tail. -/
theorem exposingTail_pos (N : ℕ) : 0 < exposingTail N := by
  obtain ⟨n,hn,hp⟩ := ((eventually_ge_atTop (max 2 (N+1))).and exposingWeight_eventually_pos).exists
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hNn : N < n := by have := (le_max_right 2 (N+1)).trans hn; omega
  have hmajor : 0 < exposingMajorant n := by
    rw [exposingMajorant,if_pos hn2,abs_of_pos hp]
    have hl : 0 < log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have := boxConst_nonneg
    positivity
  have ht := (summable_exposingTail_terms N).le_tsum n (fun j _ => by
    split_ifs <;> [exact exposingMajorant_nonneg j; exact le_rfl])
  rw [if_pos hNn] at ht
  exact hmajor.trans_le ht

end RHTower
