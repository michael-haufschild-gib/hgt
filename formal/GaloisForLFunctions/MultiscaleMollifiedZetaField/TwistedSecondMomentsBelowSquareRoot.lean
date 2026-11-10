import GaloisForLFunctions.MultiscaleMollifiedZetaField.TwistedPairsBelowSquareRoot
import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockInequality

/-!
# Twisted second moments up to every length below square root

The smoothed second moment has its two actual gcd main terms, uniformly over
bounded real coefficient sequences of length `T^θ`, for every `θ<1/2`.
The taper is sublinear and the remainder has arbitrary power saving.
-/

noncomputable section
open Complex MeasureTheory Set Finset Filter Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The actual smoothed second moment on the displaced critical line. -/
def twistedMoment (d p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∫ t, blockWindow p q η t * ‖riemannZeta (displacedLinePt d t) *
    edPoly (fun n => (w n : ℂ)) (Icc 1 N) (displacedLinePt d t)‖ ^ 2

/-- The direct and reflected gcd main terms of the product approximate
functional equation. Their opposite poles as `d→0` are retained together. -/
def twistedMomentMain (d p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) : ℂ :=
  (gcdSum₁ d N w : ℂ) * (riemannZeta ((2 * (1 / 2 - d) : ℝ) : ℂ) *
    (∫ t, blockWindowC p q η t)) +
  (gcdSum₂ d N w : ℂ) * (riemannZeta ((1 + 2 * d : ℝ) : ℂ) *
    (∫ t, blockWindowC p q η t * chiPairWeight d t))

/-- The exact error consists of the genuine coefficient-pair errors. -/
theorem twistedMoment_sub_main_eq {d x p q η : ℝ}
    (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) (N : ℕ) (w : ℕ → ℝ) :
    (twistedMoment d p q η N w : ℂ) - twistedMomentMain d p q η N w =
      ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (w h : ℂ) * (w k : ℂ) *
        pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k := by
  have hid := integral_window_normSq_eq hd (by linarith only [hd8]) hx hη hL hpq
    (fun n => (w n : ℂ)) N (fun n _ => Complex.conj_ofReal (w n))
  have hi : (twistedMoment d p q η N w : ℂ) =
      ∫ t, blockWindowC p q η t * ((‖riemannZeta (displacedLinePt d t) *
        edPoly (fun n => (w n : ℂ)) (Icc 1 N) (displacedLinePt d t)‖ ^ 2 : ℝ) : ℂ) := by
    unfold twistedMoment
    rw [← integral_ofReal]
    congr 1
    funext t
    simp only [blockWindowC, Complex.ofReal_mul]
  rw [hi, hid]
  have hpairs : ∀ h ∈ Icc 1 N, ∀ k ∈ Icc 1 N,
      (w h : ℂ) * (w k : ℂ) *
        ((∑' P : ℕ × ℕ, directTerm d x p q η h k P) +
          (∑' P : ℕ × ℕ, dualTerm d x p q η h k P) - residueTerm d x p q η h k) =
      (w h : ℂ) * (w k : ℂ) * mainTerm₁ d p q η h k +
        (w h : ℂ) * (w k : ℂ) * mainTerm₂ d p q η h k +
        (w h : ℂ) * (w k : ℂ) * pairError d x p q η (h / Nat.gcd h k) (k / Nat.gcd h k) h k := by
    intro h hh k hk
    rw [blockPair_eq_main hd hd8 hx hη hL hpq (mem_Icc.mp hh).1 (mem_Icc.mp hk).1]
    ring
  rw [sum_congr rfl fun h hh => sum_congr rfl fun k hk => hpairs h hh k hk]
  simp only [sum_add_distrib]
  rw [sum_mainTerm₁_eq (a := w) (fun _ _ => rfl),
    sum_mainTerm₂_eq (a := w) (fun _ _ => rfl)]
  unfold twistedMomentMain
  ring

/-- The full two-main-term twisted moment formula for every mollifier
exponent below `1/2`, with arbitrary power saving in its actual remainder. -/
theorem exists_twistedMoment_power_saving {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (B : ℝ) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q : ℝ) (N : ℕ) (w : ℕ → ℝ),
        T ≤ q → q ≤ 2 * T → 0 < d → d ≤ 1 / 20 → (N : ℝ) ≤ T ^ θ →
        (∀ n ∈ Icc 1 N, |w n| ≤ 1) →
        ‖(twistedMoment d T q (T ^ a) N w : ℂ) - twistedMomentMain d T q (T ^ a) N w‖ ≤
          (q - T + 2 * T ^ a) * C * T ^ (-B) := by
  obtain ⟨a, C, ha, ha1, hC, hpair⟩ := exists_pairError_power_saving hθ0 hθ (B + 2 * θ)
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_rpow_le_quarter ha1, hpair]
    with T hT hη hp
  intro d q N w hq hq2 hd hd20 hN hw
  have hT0 : 0 < T := by linarith only [hT]
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hL : 4 ≤ T - T ^ a := by linarith only [hT, hη]
  have hval : 0 ≤ (q - T + 2 * T ^ a) * C * T ^ (-(B + 2 * θ)) := by positivity
  rw [twistedMoment_sub_main_eq hd (by linarith only [hd20]) hT0 hη0 hL hq N w]
  have hterm : ∀ h ∈ Icc 1 N, ∀ k ∈ Icc 1 N,
      ‖(w h : ℂ) * (w k : ℂ) * pairError d T T q (T ^ a)
        (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖ ≤
      (q - T + 2 * T ^ a) * C * T ^ (-(B + 2 * θ)) := by
    intro h hh k hk
    have hwh : ‖(w h : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hw h hh
    have hwk : ‖(w k : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hw k hk
    have hc : ‖(w h : ℂ)‖ * ‖(w k : ℂ)‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hwh hwk (norm_nonneg _) zero_le_one
    have herr := hp d q h k hq hq2 hd hd20 (mem_Icc.mp hh).1 (mem_Icc.mp hk).1
      ((by exact_mod_cast (mem_Icc.mp hh).2 : (h : ℝ) ≤ N).trans hN)
      ((by exact_mod_cast (mem_Icc.mp hk).2 : (k : ℝ) ≤ N).trans hN)
    rw [norm_mul, norm_mul]
    simpa only [one_mul] using mul_le_mul hc herr (norm_nonneg _) zero_le_one
  have hN2 : (N : ℝ) ^ 2 ≤ T ^ (2 * θ) := by
    calc
      _ ≤ (T ^ θ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; congr 1; ring
  calc
    _ ≤ ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
        ‖(w h : ℂ) * (w k : ℂ) * pairError d T T q (T ^ a)
          (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun h _ => norm_sum_le _ _)
    _ ≤ ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
        (q - T + 2 * T ^ a) * C * T ^ (-(B + 2 * θ)) :=
      sum_le_sum fun h hh => sum_le_sum fun k hk => hterm h hh k hk
    _ = (N : ℝ) ^ 2 * ((q - T + 2 * T ^ a) * C * T ^ (-(B + 2 * θ))) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ T ^ (2 * θ) * ((q - T + 2 * T ^ a) * C * T ^ (-(B + 2 * θ))) :=
      mul_le_mul_of_nonneg_right hN2 hval
    _ = _ := by
      have he : T ^ (2 * θ) * T ^ (-(B + 2 * θ)) = T ^ (-B) := by
        rw [← Real.rpow_add hT0]
        congr 1
        ring
      calc
        _ = ((q - T + 2 * T ^ a) * C) * (T ^ (2 * θ) * T ^ (-(B + 2 * θ))) := by ring
        _ = _ := by rw [he]

end GaloisForLFunctions.MultiscaleMollifiedZetaField

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_twistedMoment_power_saving
