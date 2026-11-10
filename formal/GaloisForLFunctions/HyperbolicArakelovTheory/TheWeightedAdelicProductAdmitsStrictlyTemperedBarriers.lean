import GaloisForLFunctions.HyperbolicArakelovTheory.ThePositiveSquareRootOfTheAdelicPrecision
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strictly tempered barriers for the weighted adelic adjacency

The all-prime spectral parameter is continuous at the tempered edge. The
hyperbolic spectral shift therefore leaves room for a radial exponent strictly
above one half. Its restricted product is an actual positive supersolution
for the original prime sum, with an unconditional positive spectral margin.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency AdelicRadial AdelicGreen CoupledProductObstruction SurfaceOfSpecZ

private theorem prime_pos (p : Prime) : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
private theorem prime_one_lt (p : Prime) : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt

/-- Weighted local spectral parameter at a common radial exponent. -/
def spectralTerm (s : ℝ) (p : Prime) : ℝ := weight p * treeEigen p.1 s

def spectralEdge (s : ℝ) : ℝ := ∑' p : Prime, spectralTerm s p

theorem spectralTerm_pos (s : ℝ) (p : Prime) : 0 < spectralTerm s p :=
  mul_pos (weight_pos p) (add_pos (Real.rpow_pos_of_pos (prime_pos p) _)
    (Real.rpow_pos_of_pos (prime_pos p) _))

private theorem spectralTerm_rpow (s : ℝ) (p : Prime) :
    spectralTerm s p = (p.1 : ℝ) ^ (s - 2) + (p.1 : ℝ) ^ ((1 - s) - 2) := by
  rw [Real.rpow_sub (prime_pos p), Real.rpow_sub (prime_pos p), Real.rpow_two]
  unfold spectralTerm weight treeEigen
  ring

private theorem spectralTerm_le (s : ℝ) (hs₁ : 1 / 4 ≤ s) (hs₂ : s ≤ 3 / 4) (p : Prime) :
    spectralTerm s p ≤ 2 * (p.1 : ℝ) ^ (-5 / 4 : ℝ) := by
  rw [spectralTerm_rpow]
  have h₁ := Real.rpow_le_rpow_of_exponent_le (prime_one_lt p).le
    (show s - 2 ≤ (-5 / 4 : ℝ) by linarith only [hs₂])
  have h₂ := Real.rpow_le_rpow_of_exponent_le (prime_one_lt p).le
    (show (1 - s) - 2 ≤ (-5 / 4 : ℝ) by linarith only [hs₁])
  linarith only [h₁, h₂]

private theorem summable_spectral_majorant :
    Summable (fun p : Prime => 2 * (p.1 : ℝ) ^ (-5 / 4 : ℝ)) :=
  ((Real.summable_nat_rpow.mpr (by norm_num : (-5 / 4 : ℝ) < -1)).subtype Nat.Prime).mul_left 2

theorem summable_spectralTerm (s : ℝ) (hs₁ : 1 / 4 ≤ s) (hs₂ : s ≤ 3 / 4) :
    Summable (spectralTerm s) :=
  Summable.of_nonneg_of_le (fun p => (spectralTerm_pos s p).le)
    (spectralTerm_le s hs₁ hs₂) summable_spectral_majorant

theorem spectralTerm_half (p : Prime) : spectralTerm (1 / 2) p = edgeTerm p := by
  rw [spectralTerm, (treeEigen_eq_iff (prime_one_lt p) (1 / 2)).mpr rfl]
  rfl

/-- The infinite set of places does not consume the positive hyperbolic spectral shift. -/
theorem tendsto_spectralEdge_half : Tendsto spectralEdge (𝓝 (1 / 2 : ℝ)) (𝓝 edge) := by
  have ht (p : Prime) : Tendsto (fun s => spectralTerm s p) (𝓝 (1 / 2 : ℝ))
      (𝓝 (spectralTerm (1 / 2) p)) := by
    have h₁ := (Real.continuous_const_rpow (prime_pos p).ne').tendsto (1 / 2 : ℝ)
    have h₂ : Tendsto (fun s : ℝ => (p.1 : ℝ) ^ (1 - s)) (𝓝 (1 / 2 : ℝ))
        (𝓝 ((p.1 : ℝ) ^ ((1 : ℝ) - 1 / 2))) := by
      have hc : Continuous (fun s : ℝ => (1 : ℝ) - s) := continuous_const.sub continuous_id
      exact ((Real.continuous_const_rpow (prime_pos p).ne').comp hc).tendsto (1 / 2 : ℝ)
    exact (tendsto_const_nhds (x := weight p)).mul (h₁.add h₂)
  have hb : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), ∀ p : Prime,
      ‖spectralTerm s p‖ ≤ 2 * (p.1 : ℝ) ^ (-5 / 4 : ℝ) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)] with s hs p
    rw [Real.norm_eq_abs, abs_of_pos (spectralTerm_pos s p)]
    exact spectralTerm_le s hs.1.le hs.2.le p
  have h := tendsto_tsum_of_dominated_convergence summable_spectral_majorant ht hb
  change Tendsto (fun s => ∑' p : Prime, spectralTerm s p) (𝓝 (1 / 2 : ℝ)) (𝓝 edge)
  simpa only [spectralTerm_half, edge] using h

private theorem exists_barrierExponent : ∃ s : ℝ,
    1 / 2 < s ∧ s ≤ 3 / 4 ∧ spectralEdge s < edge + 1 / 4 := by
  have h := tendsto_spectralEdge_half.eventually
    (gt_mem_nhds (show edge < edge + 1 / 4 by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε₈ : ε ≤ 1 / 8 := min_le_right _ _
  refine ⟨1 / 2 + ε, by linarith, by linarith, hball ?_⟩
  simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hε] using hεδ

/-- One exponent selected by the proved all-prime spectral margin. -/
def barrierExponent : ℝ := Classical.choose exists_barrierExponent

theorem barrierExponent_gt_half : (1 / 2 : ℝ) < barrierExponent :=
  (Classical.choose_spec exists_barrierExponent).1

theorem barrierExponent_le : barrierExponent ≤ 3 / 4 :=
  (Classical.choose_spec exists_barrierExponent).2.1

def barrierEnergy : ℝ := spectralEdge barrierExponent

theorem barrierEnergy_lt : barrierEnergy < edge + 1 / 4 :=
  (Classical.choose_spec exists_barrierExponent).2.2

theorem summable_barrier_spectralTerm : Summable (spectralTerm barrierExponent) :=
  summable_spectralTerm _ (by linarith only [barrierExponent_gt_half]) barrierExponent_le

theorem barrierEnergy_pos : 0 < barrierEnergy :=
  (spectralTerm_pos barrierExponent ⟨2, Nat.prime_two⟩).trans_le
    (summable_barrier_spectralTerm.le_tsum ⟨2, Nat.prime_two⟩
      (fun p _ => (spectralTerm_pos barrierExponent p).le))

def barrierGap : ℝ := Real.sqrt (rootScale ^ 2 - barrierEnergy)
def barrierRemainder : ℝ := rootScale - barrierGap

theorem barrierGap_pos : 0 < barrierGap := by
  apply Real.sqrt_pos.mpr
  rw [rootScale_sq]
  exact sub_pos.mpr barrierEnergy_lt

theorem barrierGap_sq : barrierGap ^ 2 = rootScale ^ 2 - barrierEnergy :=
  Real.sq_sqrt (by rw [rootScale_sq]; exact sub_nonneg.mpr barrierEnergy_lt.le)

theorem barrierRemainder_pos : 0 < barrierRemainder := by
  unfold barrierRemainder
  nlinarith only [barrierGap_sq, barrierEnergy_pos, barrierGap_pos, rootScale_pos]

theorem barrierRemainder_lt_scale : barrierRemainder < rootScale := by
  unfold barrierRemainder
  linarith only [barrierGap_pos]

theorem barrierRemainder_identity :
    barrierEnergy + barrierRemainder ^ 2 = 2 * rootScale * barrierRemainder := by
  unfold barrierRemainder
  nlinarith only [barrierGap_sq]

/-- Radial product at an arbitrary common exponent, defined on the actual restricted carrier. -/
def powerProfile (s : ℝ) (x y : FiniteVertices) : ℝ := finiteGreenProduct x y ^ (2 * s)

theorem powerProfile_pos (s : ℝ) (x y : FiniteVertices) : 0 < powerProfile s x y :=
  Real.rpow_pos_of_pos (product_pos x y) _

theorem powerProfile_self (s : ℝ) (x : FiniteVertices) : powerProfile s x x = 1 := by
  rw [powerProfile, product_self, Real.one_rpow]

theorem powerProfile_smul (s : ℝ) (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    powerProfile s (a • x) (a • y) = powerProfile s x y := by
  rw [powerProfile, powerProfile, finiteGreenProduct_smul]

private theorem localFactor_half (p : Prime) (x y : LocalVertex p) :
    localFactor p x y = localRatio p x y ^ (1 / 2 : ℝ) := by
  have hc := PrimeFibres.normalized_localGreen p x x
  rw [localGreen_self, localFactor_self] at hc
  have h := PrimeFibres.normalized_localGreen p x y
  rw [localGreen, ← mul_assoc, hc, one_mul] at h
  exact h.symm

private theorem localFactor_power (p : Prime) (s : ℝ) (x y : LocalVertex p) :
    localFactor p x y ^ (2 * s) = localRatio p x y ^ s := by
  rw [localFactor_half, ← Real.rpow_mul (localRatio_pos p x y).le]
  congr 1
  ring

theorem powerProfile_replace (p : Prime) (s : ℝ) (x y : FiniteVertices) (z : LocalVertex p) :
    powerProfile s x (replaceVertex p y z) =
      powerProfile s x y * localRatio p (x.1 p) z ^ s / localRatio p (x.1 p) (y.1 p) ^ s := by
  rw [powerProfile, product_replace, Real.div_rpow
    (mul_pos (product_pos x y) (localFactor_pos p _ _)).le (localFactor_pos p _ _).le,
    Real.mul_rpow (product_pos x y).le (localFactor_pos p _ _).le,
    localFactor_power, localFactor_power]
  rfl

private theorem local_power_row_le (p : Prime) (s : ℝ) (hs : 0 < s) (x y : LocalVertex p) :
    (∑ z ∈ neighbors p y, localRatio p x z ^ s) ≤ treeEigen p.1 s * localRatio p x y ^ s := by
  have hc : 0 < treeGreen p.1 s 0 := by
    simpa only [localGreen_self] using localGreen_pos p hs x x
  have hr := localGreen_resolvent p hs x y
  simp only [localGreen, ← Finset.mul_sum] at hr
  have hi : (0 : ℝ) ≤ if x = y then 1 else 0 := by split_ifs <;> norm_num
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ treeEigen p.1 s * (treeGreen p.1 s 0 * localRatio p x y ^ s) := by linarith only [hr, hi]
    _ = _ := by ring

theorem localAdj_powerProfile_le (p : Prime) (s : ℝ) (hs : 0 < s) (x y : FiniteVertices) :
    localAdj p (powerProfile s x) y ≤ treeEigen p.1 s * powerProfile s x y := by
  have hr : 0 < localRatio p (x.1 p) (y.1 p) ^ s :=
    Real.rpow_pos_of_pos (localRatio_pos p _ _) _
  have he : localAdj p (powerProfile s x) y =
      (powerProfile s x y / localRatio p (x.1 p) (y.1 p) ^ s) *
        ∑ z ∈ neighbors p (y.1 p), localRatio p (x.1 p) z ^ s := by
    simp only [localAdj, powerProfile_replace, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [he]
  calc
    _ ≤ (powerProfile s x y / localRatio p (x.1 p) (y.1 p) ^ s) *
        (treeEigen p.1 s * localRatio p (x.1 p) (y.1 p) ^ s) :=
      mul_le_mul_of_nonneg_left (local_power_row_le p s hs _ _)
        (div_nonneg (powerProfile_pos s x y).le hr.le)
    _ = _ := by field_simp [hr.ne']

/-- The strictly tempered profile chosen from the actual all-prime spectral margin. -/
def barrierProfile (x y : FiniteVertices) : ℝ := powerProfile barrierExponent x y

theorem barrierProfile_pos (x y : FiniteVertices) : 0 < barrierProfile x y :=
  powerProfile_pos _ x y

theorem barrierProfile_self (x : FiniteVertices) : barrierProfile x x = 1 :=
  powerProfile_self _ x

private theorem placeTerm_barrierProfile_le (p : Prime) (x y : FiniteVertices) :
    placeTerm p (barrierProfile x) y ≤ spectralTerm barrierExponent p * barrierProfile x y := by
  have h := mul_le_mul_of_nonneg_left
    (localAdj_powerProfile_le p barrierExponent (by linarith only [barrierExponent_gt_half]) x y)
    (weight_pos p).le
  have he : barrierProfile x = powerProfile barrierExponent x := by funext y; rfl
  rw [placeTerm, spectralTerm, he]
  simpa only [mul_assoc] using h

theorem barrierProfile_inDomain (x : FiniteVertices) : InDomain (barrierProfile x) := by
  intro y
  exact Summable.of_nonneg_of_le (fun p => placeTerm_nonneg p (fun z => (barrierProfile_pos x z).le) y)
    (fun p => placeTerm_barrierProfile_le p x y) (summable_barrier_spectralTerm.mul_right _)

/-- A positive product supersolution with a strictly positive hyperbolic spectral gap. -/
theorem adjacency_barrierProfile_le (x y : FiniteVertices) :
    adjacency (barrierProfile x) y ≤ barrierEnergy * barrierProfile x y := by
  calc
    _ ≤ ∑' p : Prime, spectralTerm barrierExponent p * barrierProfile x y :=
      (barrierProfile_inDomain x y).tsum_le_tsum (fun p => placeTerm_barrierProfile_le p x y)
        (summable_barrier_spectralTerm.mul_right _)
    _ = barrierEnergy * barrierProfile x y := by rw [tsum_mul_right]; rfl

#print axioms tendsto_spectralEdge_half
#print axioms barrierExponent_gt_half
#print axioms barrierEnergy_lt
#print axioms barrierRemainder_identity
#print axioms barrierProfile_inDomain
#print axioms adjacency_barrierProfile_le

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
