import GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchurSupport
import GaloisForLFunctions.BiScaleUncertainty.SignedCosetProductCoupling

/-!
# Optimized dyadic coefficient splitting

The frame `{0, log 2, 2 log 2}` and targets `y, y + log 2` give two overlapping
three-coordinate columns. Splitting the two repeated coefficients optimizes a
compact square of exact Schur bounds. Every frame and target orthogonality is
derived from the actual source's logarithmic grid zeros through four.
-/

set_option autoImplicit false
open Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace DyadicSchur
open TwoColumnSchur

def leftWeights (W a b : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1 * W, p.2 * a, b]
def rightWeights (W a c : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ![c, (1 - p.1) * W, (1 - p.2) * a]
def splitSupport (W a b c : ℝ) (p : ℝ × ℝ) : ℝ :=
  support Finset.univ (leftWeights W a b p) (rightWeights W a c p)
def splitSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
def optimizedSupport (W a b c : ℝ) : ℝ := sInf (splitSupport W a b c '' splitSquare)

theorem continuous_splitSupport :
    Continuous (fun q : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
      splitSupport q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  unfold splitSupport support energy pairing leftWeights rightWeights
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  fun_prop

theorem continuous_optimizedSupport :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ => optimizedSupport q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  (isCompact_Icc.prod isCompact_Icc).continuous_sInf continuous_splitSupport

theorem optimizedSupport_attained (W a b c : ℝ) :
    ∃ p ∈ splitSquare, optimizedSupport W a b c = splitSupport W a b c p ∧
      ∀ q ∈ splitSquare, optimizedSupport W a b c ≤ splitSupport W a b c q := by
  have hc : Continuous (splitSupport W a b c) := by
    unfold splitSupport support energy pairing leftWeights rightWeights
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    fun_prop
  obtain ⟨p, hp, he, hm⟩ := (show IsCompact splitSquare from isCompact_Icc.prod isCompact_Icc).exists_sInf_image_eq_and_le
    (show splitSquare.Nonempty from ⟨(0, 0), by simp [splitSquare]⟩) hc.continuousOn
  exact ⟨p, hp, he, fun q hq => he.trans_le (hm q hq)⟩

theorem splitSupport_bound (W a b c u₀ u₁ u₂ v R : ℝ) (p : ℝ × ℝ)
    (hR : 0 ≤ R) (hf : Feasible Finset.univ ![u₀, u₁, u₂] ![v, u₀, u₁] R) :
    W * u₀ + a * u₁ + b * u₂ + c * v ≤ R * splitSupport W a b c p := by
  have h := pairing_le_support Finset.univ (leftWeights W a b p) (rightWeights W a c p)
    ![u₀, u₁, u₂] ![v, u₀, u₁] hR hf
  change _ ≤ R * splitSupport W a b c p at h
  simp only [pairing, leftWeights, rightWeights, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero] at h
  nlinarith

theorem optimizedSupport_bound (W a b c u₀ u₁ u₂ v R : ℝ)
    (hR : 0 ≤ R) (hf : Feasible Finset.univ ![u₀, u₁, u₂] ![v, u₀, u₁] R) :
    W * u₀ + a * u₁ + b * u₂ + c * v ≤ R * optimizedSupport W a b c := by
  obtain ⟨p, _, he, _⟩ := optimizedSupport_attained W a b c
  rw [he]
  exact splitSupport_bound W a b c u₀ u₁ u₂ v R p hR hf

/-- Repeated origin coordinates force support at least `W`, uniformly in the split. -/
theorem origin_le_optimizedSupport (W a b c : ℝ) : W ≤ optimizedSupport W a b c := by
  have hf : Feasible (Finset.univ : Finset (Fin 3)) ![1, 0, 0] ![0, 1, 0] 1 := by
    norm_num [Feasible, energy, pairing, Fin.sum_univ_succ]
  simpa using optimizedSupport_bound W a b c 1 0 0 0 1 (by norm_num) hf

theorem splitSupport_le_mass {W a b c : ℝ} (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) {p : ℝ × ℝ} (hp : p ∈ splitSquare) :
    splitSupport W a b c p ≤ W + a + b + c := by
  have hn (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      collarBlockSize Finset.univ (![x, y, z] : Fin 3 → ℝ) ≤ x + y + z := by
    have hs := blockSize_sq Finset.univ (![x, y, z] : Fin 3 → ℝ)
    simp [energy, Fin.sum_univ_succ] at hs
    have hnn : 0 ≤ collarBlockSize Finset.univ (![x, y, z] : Fin 3 → ℝ) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  have hl := hn (p.1 * W) (p.2 * a) b (mul_nonneg hp.1.1 hW) (mul_nonneg hp.2.1 ha) hb
  have hr := hn c ((1 - p.1) * W) ((1 - p.2) * a) hc
    (mul_nonneg (sub_nonneg.mpr hp.1.2) hW) (mul_nonneg (sub_nonneg.mpr hp.2.2) ha)
  have h := support_le_independent Finset.univ (leftWeights W a b p) (rightWeights W a c p)
  change splitSupport W a b c p ≤ _ at h
  change collarBlockSize Finset.univ (leftWeights W a b p) ≤ _ at hl
  change collarBlockSize Finset.univ (rightWeights W a c p) ≤ _ at hr
  nlinarith

theorem optimizedSupport_le_mass {W a b c : ℝ} (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) : optimizedSupport W a b c ≤ W + a + b + c := by
  obtain ⟨p, hp, he, _⟩ := optimizedSupport_attained W a b c
  rw [he]
  exact splitSupport_le_mass hW ha hb hc hp

def frame : Fin 3 → ℝ := ![0, Real.log 2, 2 * Real.log 2]

theorem source_frame_orthogonal {n : ℕ} (hn : 2 ≤ n) (f : LogarithmicGridSource n) :
    ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      i ≠ j → autocorr f.1 (frame i - frame j) = 0 := by
  have h₁ : autocorr f.1 (Real.log 2) = 0 := by
    simpa [logarithmicCollarNode] using f.2 0 (Finset.mem_range.mpr (by omega))
  have h₂ : autocorr f.1 (2 * Real.log 2) = 0 := by
    have h := f.product_zero (a := 2) (b := 2) le_rfl le_rfl (by omega)
    norm_num at h
    convert h using 1; congr 1; ring
  have hn₁ : autocorr f.1 (-Real.log 2) = 0 := by rw [autocorr_neg, h₁]
  have hn₂ : autocorr f.1 (-(2 * Real.log 2)) = 0 := by rw [autocorr_neg, h₂]
  intro i _ j _ hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals norm_num [frame]
  all_goals solve | exact h₁ | exact h₂ | exact hn₁ | exact hn₂ |
    (convert hn₁ using 1; congr 1; ring) | (convert h₁ using 1; congr 1; ring)

/-- Actual source data supply the full residual determinant, not only two spheres. -/
theorem source_feasible {n : ℕ} (hn : 2 ≤ n) (f : LogarithmicGridSource n) (y : ℝ) :
    Feasible Finset.univ
      ![autocorr f.1 y, autocorr f.1 (Real.log 2 - y), autocorr f.1 (2 * Real.log 2 - y)]
      ![autocorr f.1 (Real.log 2 + y), autocorr f.1 y, autocorr f.1 (Real.log 2 - y)]
      (autocorr f.1 0) := by
  have ho := source_frame_orthogonal hn f
  have hl := autocorr_finset_bessel_sq_le f.1.hasCompactSupport f.1.continuous Finset.univ frame ho y
  have hr := autocorr_finset_bessel_sq_le f.1.hasCompactSupport f.1.continuous Finset.univ frame ho (y + Real.log 2)
  have hlag : autocorr f.1 (y + Real.log 2 - y) = 0 := by
    rw [add_sub_cancel_left]
    simpa [logarithmicCollarNode] using f.2 0 (Finset.mem_range.mpr (by omega))
  have hd := autocorr_collar_inner_sq_le_of_zero_lag f.1.hasCompactSupport f.1.continuous
    Finset.univ frame ho hlag
  have he (x : ℝ) : autocorr f.1 (y - x) = autocorr f.1 (x - y) := by
    rw [show y - x = -(x - y) by ring, autocorr_neg]
  have hu : (fun i => autocorr f.1 (y - frame i)) =
      ![autocorr f.1 y, autocorr f.1 (Real.log 2 - y), autocorr f.1 (2 * Real.log 2 - y)] := by
    funext i
    fin_cases i <;> simp [frame, he]
  have hv : (fun i => autocorr f.1 (y + Real.log 2 - frame i)) =
      ![autocorr f.1 (Real.log 2 + y), autocorr f.1 y, autocorr f.1 (Real.log 2 - y)] := by
    funext i
    fin_cases i
    · change autocorr f.1 (y + Real.log 2 - 0) = autocorr f.1 (Real.log 2 + y)
      congr 1; ring
    · change autocorr f.1 (y + Real.log 2 - Real.log 2) = autocorr f.1 y
      congr 1; ring
    · change autocorr f.1 (y + Real.log 2 - 2 * Real.log 2) = autocorr f.1 (Real.log 2 - y)
      rw [show y + Real.log 2 - 2 * Real.log 2 = y - Real.log 2 by ring, he]
  change energy Finset.univ (fun i => autocorr f.1 (y - frame i)) ≤ _ at hl
  change energy Finset.univ (fun i => autocorr f.1 (y + Real.log 2 - frame i)) ≤ _ at hr
  change pairing Finset.univ (fun i => autocorr f.1 (y - frame i))
    (fun i => autocorr f.1 (y + Real.log 2 - frame i)) ^ 2 ≤
    (autocorr f.1 0 ^ 2 - energy Finset.univ (fun i => autocorr f.1 (y - frame i))) *
    (autocorr f.1 0 ^ 2 - energy Finset.univ (fun i => autocorr f.1 (y + Real.log 2 - frame i))) at hd
  rw [hu] at hl
  rw [hv] at hr
  rw [hu, hv] at hd
  exact ⟨hl, hr, hd⟩

/-- Optimized four-coordinate support for every actual continuous compact grid source. -/
theorem source_weighted_bound {n : ℕ} (hn : 2 ≤ n) (f : LogarithmicGridSource n)
    (y W a b c : ℝ) :
    W * autocorr f.1 y + a * autocorr f.1 (Real.log 2 - y) +
      b * autocorr f.1 (2 * Real.log 2 - y) + c * autocorr f.1 (Real.log 2 + y) ≤
        autocorr f.1 0 * optimizedSupport W a b c :=
  optimizedSupport_bound _ _ _ _ _ _ _ _ _ (autocorr_zero_nonneg f.1) (source_feasible hn f y)

/-- Symbolic strict separation from the one-column sphere relaxation. -/
theorem optimizedSupport_strict_sphere_example : optimizedSupport 1 1 1 0 < Real.sqrt 3 := by
  obtain ⟨_, _, _, hmin⟩ := optimizedSupport_attained 1 1 1 0
  have h := hmin (1 / 2, 1 / 2) (by norm_num [splitSquare])
  have he : splitSupport 1 1 1 0 (1 / 2, 1 / 2) ^ 2 = 2 + 2 * Real.sqrt (3 / 16) := by
    have hs := support_sq Finset.univ (leftWeights 1 1 1 (1 / 2, 1 / 2))
      (rightWeights 1 1 0 (1 / 2, 1 / 2))
    norm_num [splitSupport, energy, pairing, leftWeights, rightWeights, Fin.sum_univ_succ] at hs ⊢
    exact hs
  have hd := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 16)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  have hn := Real.sqrt_nonneg (3 / 16 : ℝ)
  have hdlt : Real.sqrt (3 / 16 : ℝ) < 1 / 2 := by nlinarith
  have hlt : splitSupport 1 1 1 0 (1 / 2, 1 / 2) < Real.sqrt 3 := by nlinarith
  exact h.trans_lt hlt

end DyadicSchur
end
end GaloisForLFunctions.BiScaleUncertainty
