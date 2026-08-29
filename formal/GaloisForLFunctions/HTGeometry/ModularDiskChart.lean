import Mathlib.Analysis.Complex.OpenMapping
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingLift
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingMarty
import GaloisForLFunctions.Bottcher.DiskSchwarzPick

/-!
# The modular covering in the disc chart

`modularDisk = λ ∘ cayleyInv` reads the modular covering `λ : ℍ → ℂ∖{0,1}` as a holomorphic
surjection from the open unit disc onto `ℂ∖{0,1}`.  Because it is an open map, every compact subset
of `ℂ∖{0,1}` is already covered by the image of a strictly smaller disc — the uniformity that turns
the modular lift of an omitting family into a *quantitative* bound.

* `modularDisk`, `analyticOnNhd_modularDisk`, `exists_modularDisk_eq` — the chart, its analyticity
  and its surjectivity.
* `isOpen_modularDisk_image` — the open mapping property.
* `exists_radius_lt_one_modularDisk_covers` — **a compact set of values lifts into a fixed
  sub-disc.**
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Complex Metric Set

noncomputable section

/-- The modular covering read in the disc chart: `λ ∘ cayleyInv`. -/
def modularDisk (w : ℂ) : ℂ := modularLambda (cayleyInv w)

theorem ne_one_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  intro h
  rw [h, norm_one] at hw
  linarith

theorem modularDisk_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : modularDisk w ≠ 0 :=
  (modularLambda_omits_zero_one' (cayleyInv_im_pos_of_norm_lt_one hw)).1

theorem modularDisk_ne_one {w : ℂ} (hw : ‖w‖ < 1) : modularDisk w ≠ 1 :=
  (modularLambda_omits_zero_one' (cayleyInv_im_pos_of_norm_lt_one hw)).2

theorem differentiableOn_cayleyInv_ball : DifferentiableOn ℂ cayleyInv (ball (0 : ℂ) 1) := by
  intro y hy
  have hyn : ‖y‖ < 1 := by simpa [mem_ball, dist_zero_right] using hy
  exact (cayleyInv_differentiableAt (ne_one_of_norm_lt_one hyn)).differentiableWithinAt

theorem analyticOnNhd_modularDisk : AnalyticOnNhd ℂ modularDisk (ball (0 : ℂ) 1) := by
  intro w hw
  have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  have hcinv : AnalyticAt ℂ cayleyInv w :=
    (differentiableOn_cayleyInv_ball.analyticOnNhd isOpen_ball) w hw
  have hlam : AnalyticAt ℂ modularLambda (cayleyInv w) :=
    analyticAt_modularLambda (cayleyInv_im_pos_of_norm_lt_one hwn)
  exact hlam.comp hcinv

/-- **The chart is onto `ℂ∖{0,1}`.** -/
theorem exists_modularDisk_eq {v : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    ∃ w : ℂ, ‖w‖ < 1 ∧ modularDisk w = v := by
  obtain ⟨τ, hτ, hlam⟩ := modularLambda_surjective (w := v) (by simp [hv0, hv1])
  have hτI : τ + Complex.I ≠ 0 := by
    intro h
    have : τ = -Complex.I := by linear_combination h
    rw [this] at hτ
    simp at hτ
    linarith
  refine ⟨cayley τ, cayley_norm_lt_one hτ, ?_⟩
  rw [modularDisk, cayleyInv_cayley hτI]
  exact hlam

/-- **The chart is an open map on the disc.** -/
theorem isOpen_modularDisk_image {s : Set ℂ} (hs : s ⊆ ball (0 : ℂ) 1) (hso : IsOpen s) :
    IsOpen (modularDisk '' s) := by
  have hpre : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  rcases AnalyticOnNhd.is_constant_or_isOpen analyticOnNhd_modularDisk hpre with hconst | hopen
  · exfalso
    obtain ⟨c, hc⟩ := hconst
    obtain ⟨w₂, hw₂, hv₂⟩ := exists_modularDisk_eq (v := 2) (by norm_num) (by norm_num)
    obtain ⟨w₃, hw₃, hv₃⟩ := exists_modularDisk_eq (v := 3) (by norm_num) (by norm_num)
    have h₂ : modularDisk w₂ = c := hc w₂ (by simpa [mem_ball, dist_zero_right] using hw₂)
    have h₃ : modularDisk w₃ = c := hc w₃ (by simpa [mem_ball, dist_zero_right] using hw₃)
    rw [hv₂] at h₂
    rw [hv₃] at h₃
    rw [← h₂] at h₃
    norm_num at h₃
  · exact hopen s hs hso

/-- **A compact set of values lifts into a fixed sub-disc.**  Since the chart is an open surjection
onto `ℂ∖{0,1}`, the increasing open sets `modularDisk '' ball 0 (1 − 1/(n+2))` exhaust `ℂ∖{0,1}`, so
a compact `K` avoiding `0` and `1` is already covered by one of them. -/
theorem exists_radius_lt_one_modularDisk_covers {K : Set ℂ} (hK : IsCompact K)
    (hK0 : ∀ v ∈ K, v ≠ 0) (hK1 : ∀ v ∈ K, v ≠ 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < 1 ∧ ∀ v ∈ K, ∃ w : ℂ, ‖w‖ < s₀ ∧ modularDisk w = v := by
  classical
  set rad : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hrad
  have hrad0 : ∀ n, 0 < rad n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hrad]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  have hrad1 : ∀ n, rad n < 1 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    rw [hrad]; linarith
  have hradmono : Monotone rad := by
    intro m n hmn
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
      apply one_div_le_one_div_of_le <;> linarith
    rw [hrad]; simp only; linarith
  set U : ℕ → Set ℂ := fun n => modularDisk '' ball (0 : ℂ) (rad n) with hU
  have hUopen : ∀ n, IsOpen (U n) := by
    intro n
    refine isOpen_modularDisk_image ?_ isOpen_ball
    exact ball_subset_ball (le_of_lt (hrad1 n))
  have hUmono : ∀ {m n : ℕ}, m ≤ n → U m ⊆ U n := by
    intro m n hmn
    exact Set.image_mono (ball_subset_ball (hradmono hmn))
  have hcover : K ⊆ ⋃ n, U n := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := exists_modularDisk_eq (hK0 v hv) (hK1 v hv)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ‖w‖))
    have hpos : 0 < 1 - ‖w‖ := by linarith
    have hlt : ‖w‖ < rad n := by
      have h1 : 1 / ((n : ℝ) + 2) < 1 - ‖w‖ := by
        rw [div_lt_iff₀ (by positivity)]
        have hinv : 1 / (1 - ‖w‖) < (n : ℝ) + 2 := by linarith
        rw [div_lt_iff₀ hpos] at hinv
        linarith
      rw [hrad]; linarith
    exact Set.mem_iUnion.mpr ⟨n, ⟨w, by simpa [mem_ball, dist_zero_right] using hlt, hwv⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hcover
  by_cases htne : t.Nonempty
  · obtain ⟨N, -, hN⟩ := t.exists_max_image id htne
    refine ⟨rad N, hrad0 N, hrad1 N, ?_⟩
    intro v hv
    obtain ⟨n, hn, hvn⟩ := Set.mem_iUnion₂.mp (ht hv)
    have hle : n ≤ N := hN n hn
    obtain ⟨w, hw, hwv⟩ := hUmono hle hvn
    exact ⟨w, by simpa [mem_ball, dist_zero_right] using hw, hwv⟩
  · refine ⟨rad 0, hrad0 0, hrad1 0, ?_⟩
    intro v hv
    exfalso
    have := ht hv
    rw [Finset.not_nonempty_iff_eq_empty.mp htne] at this
    simp at this


/-! ## Schottky over a compact base set -/

/-- `cayley ∘ cayleyInv = id` on the open unit disc. -/
theorem cayley_cayleyInv {w : ℂ} (hw : ‖w‖ < 1) : cayley (cayleyInv w) = w := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_norm_lt_one hw))
  have hden : cayleyInv w + Complex.I ≠ 0 := by
    rw [cayleyInv]
    have hval : Complex.I * ((1 + w) / (1 - w)) + Complex.I
        = Complex.I * (2 / (1 - w)) := by field_simp; ring
    rw [hval]
    exact mul_ne_zero Complex.I_ne_zero (div_ne_zero two_ne_zero h1)
  rw [cayley, div_eq_iff hden, cayleyInv]
  field_simp
  ring

/-- The Blaschke identity `|1 − ā b|² − |b − a|² = (1 − |a|²)(1 − |b|²)`. -/
theorem normSq_blaschke_identity (a b : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * b) - Complex.normSq (b - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- **The pseudo-hyperbolic step.**  If the Blaschke factor based at `a` has norm at most `ρ < 1`
and `‖a‖ ≤ s₀ < 1`, then `‖b‖` stays below an explicit bound `< 1`. -/
theorem norm_le_of_blaschke_le {a b : ℂ} {ρ s₀ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hs₀ : ‖a‖ ≤ s₀) (hs₀1 : s₀ < 1) (hb : ‖b‖ ≤ 1)
    (hblas : ‖(b - a) / (1 - (starRingEnd ℂ) a * b)‖ ≤ ρ) :
    ‖b‖ ^ 2 ≤ 1 - (1 - ρ ^ 2) * (1 - s₀) ^ 2 := by
  have ha1 : ‖a‖ < 1 := lt_of_le_of_lt hs₀ hs₀1
  have hden : (1 : ℂ) - (starRingEnd ℂ) a * b ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one ha1 hb
  have hdennorm : 0 < ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ := norm_pos_iff.mpr hden
  -- the numerator bound
  have hnum : ‖b - a‖ ≤ ρ * ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ := by
    rw [norm_div, div_le_iff₀ hdennorm] at hblas
    exact hblas
  -- the identity in norms
  have hid : ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2 - ‖b - a‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    have h1 := normSq_blaschke_identity a b
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm] at h1
    exact h1
  -- the denominator lower bound
  have hlow : 1 - s₀ ≤ ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ := by
    have h1 : ‖(starRingEnd ℂ) a * b‖ ≤ s₀ := by
      rw [norm_mul, RCLike.norm_conj]
      calc ‖a‖ * ‖b‖ ≤ s₀ * 1 := by
            exact mul_le_mul hs₀ hb (norm_nonneg _) (le_trans (norm_nonneg _) hs₀)
        _ = s₀ := mul_one s₀
    have h2 := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) a * b)
    have h3 : ‖(1 : ℂ)‖ = 1 := norm_one
    calc 1 - s₀ ≤ ‖(1 : ℂ)‖ - ‖(starRingEnd ℂ) a * b‖ := by rw [h3]; linarith
      _ ≤ ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ := h2
  have hs₀0 : 0 ≤ 1 - s₀ := by linarith
  have hsq : (1 - s₀) ^ 2 ≤ ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2 := by
    exact pow_le_pow_left₀ hs₀0 hlow 2
  have hnum2 : ‖b - a‖ ^ 2 ≤ ρ ^ 2 * ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg (b - a)) hnum
    nlinarith [this, norm_nonneg (b - a), hdennorm, hρ0]
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [ha1, norm_nonneg a]
  have hbsq : ‖b‖ ^ 2 ≤ 1 := by nlinarith [hb, norm_nonneg b]
  have hρsq : (0 : ℝ) ≤ 1 - ρ ^ 2 := by nlinarith [hρ0, hρ1]
  have hA : (1 - ρ ^ 2) * (1 - s₀) ^ 2
      ≤ (1 - ρ ^ 2) * ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hρsq
  have hB : (1 - ρ ^ 2) * ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2
      ≤ ‖(1 : ℂ) - (starRingEnd ℂ) a * b‖ ^ 2 - ‖b - a‖ ^ 2 := by nlinarith [hnum2]
  have hstep2 : (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) ≤ 1 * (1 - ‖b‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ‖a‖]) (by linarith)
  linarith [hid, le_trans hA hB, hstep2]


/-- **Schottky over a compact base set.**  There is a bound `M`, depending only on the compact set
`K ⊆ ℂ∖{0,1}` and on `ρ < 1`, such that every holomorphic `f` on `ball c R` omitting `0` and `1`
whose value at the centre lies in `K` satisfies `‖f‖ ≤ M` on `ball c (ρR)`.

This is the quantitative core of the three-value normality test, obtained from the modular lift and
Schwarz–Pick without any limiting argument. -/
theorem exists_bound_of_omitting_compact_base {K : Set ℂ} (hK : IsCompact K)
    (hK0 : ∀ v ∈ K, v ≠ 0) (hK1 : ∀ v ∈ K, v ≠ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ M : ℝ, ∀ (f : ℂ → ℂ) (c : ℂ) (R : ℝ), 0 < R →
      DifferentiableOn ℂ f (ball c R) →
      (∀ z ∈ ball c R, f z ≠ 0 ∧ f z ≠ 1) →
      f c ∈ K →
      ∀ z ∈ ball c (ρ * R), ‖f z‖ ≤ M := by
  obtain ⟨s₀, hs₀0, hs₀1, hs₀cov⟩ := exists_radius_lt_one_modularDisk_covers hK hK0 hK1
  set δ : ℝ := (1 - ρ ^ 2) * (1 - s₀) ^ 2 with hδdef
  have hδpos : 0 < δ := by
    have h1 : 0 < 1 - ρ ^ 2 := by nlinarith [hρ0, hρ1]
    have h2 : 0 < (1 - s₀) ^ 2 := by positivity
    rw [hδdef]; positivity
  have hδle : δ ≤ 1 := by
    have h1 : 1 - ρ ^ 2 ≤ 1 := by nlinarith [hρ0]
    have h2 : (1 - s₀) ^ 2 ≤ 1 := by nlinarith [hs₀0, hs₀1]
    have h3 : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ0, hρ1]
    rw [hδdef]
    nlinarith [h1, h2, h3, sq_nonneg (1 - s₀)]
  set s : ℝ := Real.sqrt (1 - δ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by
    rw [hsdef]
    have h1 : 1 - δ < 1 := by linarith
    calc Real.sqrt (1 - δ) < Real.sqrt 1 := by
          exact Real.sqrt_lt_sqrt (by linarith) h1
      _ = 1 := Real.sqrt_one
  have hballsub : closedBall (0 : ℂ) s ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    rw [mem_ball, dist_zero_right]
    linarith
  have hcont : ContinuousOn modularDisk (closedBall (0 : ℂ) s) :=
    fun w hw => ((analyticOnNhd_modularDisk w (hballsub hw)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn hcont
  refine ⟨M, fun f c R hR hdiff homit hfc z hz => ?_⟩
  -- the based modular lift
  obtain ⟨w₀, hw₀, hw₀v⟩ := hs₀cov (f c) hfc
  have hw₀1 : ‖w₀‖ < 1 := lt_trans hw₀ hs₀1
  have hτ₀im : 0 < (cayleyInv w₀).im := cayleyInv_im_pos_of_norm_lt_one hw₀1
  have homit' : ∀ y ∈ ball c R, f y ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro y hy
    obtain ⟨h0, h1⟩ := homit y hy
    simp [h0, h1]
  have hlamτ : modularLambda ((⟨cayleyInv w₀, hτ₀im⟩ : UpperHalfPlane) : ℂ) = f c := by
    simpa [modularDisk] using hw₀v
  obtain ⟨g, hgdiff, hgbd, hgc, hgeq⟩ :=
    omitting_lift_member_based hR f hdiff homit' ⟨cayleyInv w₀, hτ₀im⟩ hlamτ
  have hgcval : ‖g c‖ = ‖w₀‖ := by
    rw [hgc]
    rw [cayley_cayleyInv hw₀1]
  have hgclt : ‖g c‖ < 1 := by rw [hgcval]; exact hw₀1
  have hzR : z ∈ ball c R := by
    rw [mem_ball] at hz ⊢
    have : ρ * R ≤ R := by nlinarith [hρ0, hρ1, hR]
    linarith
  -- Schwarz–Pick in the disc chart
  have hblas := blaschke_lift_norm_le_dist_div hR hgdiff hgbd hgclt hzR
  have hdistρ : dist z c / R ≤ ρ := by
    rw [div_le_iff₀ hR]
    rw [mem_ball] at hz
    linarith [hz]
  have hgzsq : ‖g z‖ ^ 2 ≤ 1 - δ :=
    norm_le_of_blaschke_le hρ0 hρ1 (by rw [hgcval]; exact le_of_lt hw₀) hs₀1
      (hgbd z hzR) (le_trans hblas hdistρ)
  have hgzs : ‖g z‖ ≤ s := by
    rw [hsdef]
    exact (Real.le_sqrt (norm_nonneg _) (by linarith : (0:ℝ) ≤ 1 - δ)).mpr hgzsq
  have hfz : f z = modularDisk (g z) := (hgeq hzR).symm
  rw [hfz]
  exact hM (g z) (by rw [mem_closedBall, dist_zero_right]; exact hgzs)

end

end GaloisForLFunctions.HTGeometry
