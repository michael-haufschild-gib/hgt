import GaloisForLFunctions.RHTower.WeilMixedResonanceLockRigidity
import GaloisForLFunctions.RHTower.WeilLockPhasePositivity

/-!
# Locks with a bounded spectrum

**Theorem** (`bounded_spectrum_lock_rigidity`).  Let `G` be a Herglotz producer for the weights
`lam`, with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j q_j ρ_j^{−(s−½)}`, where the `ρ_j > 0`
are distinct and `Σ_j |q_j| max(1, ρ_j^{−1}) < ∞`.  Suppose the frequencies with `q_j ≠ 0` have a
largest and a smallest element.  Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis
holds.  In particular this holds for every finite exponential sum (`finite_spectrum_lock_rigidity`).
No arithmetic condition on the frequencies is imposed: they may be integral, rational or
irrational, on either side of `1`.

**Proof.**
1. The lock is unimodular on the line.  On the lower line `G(s̄) = conj G(s)` gives
   `|G(1 − s)| = |G(s)|`, so `|V(s)| = 1` wherever `G(s) ≠ 0`.  Such points are dense
   (`exists_ne_zero_mem_Ioo`), and `V` is continuous.
2. `|V(½ − iy)|² = Σ_{j,k} q_j conj q_k e^{iy(log ρ_j − log ρ_k)} ≡ 1`.  The Bohr mean at the
   extreme frequency `log ρ_max − log ρ_min` is `q_max conj q_min`.  It must vanish unless the
   frequency is `0`, so the spectrum is a single point.
3. A single frequency is a linear lock phase, and `linear_twist_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- **The lock factor is unimodular on the lower critical line.** -/
theorem norm_lock_eq_one {lam : ℕ → ℝ} {Φ G V : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hVc : Continuous V)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ))
    {y : ℝ} (hy : 0 < y) : ‖V (1 / 2 - (y : ℂ) * I)‖ = 1 := by
  set sl : ℝ → ℂ := fun y => 1 / 2 - (y : ℂ) * I with hsl_def
  have hgood : ∀ y : ℝ, 0 < y → G (sl y) ≠ 0 → ‖V (sl y)‖ = 1 := by
    intro y hy hG
    have hre : 1 / 2 ≤ (sl y).re := by simp [hsl_def]
    have hline : lineS (-y / 2) = sl y := by rw [lineS_eq, hsl_def]; push_cast; ring
    have hL := hlock (-y / 2) (by linarith)
    rw [hline] at hL
    have hconj : (starRingEnd ℂ) (sl y) = 1 - sl y := by
      apply Complex.ext <;> simp [hsl_def]; norm_num
    have hc := G_conj hsl hid hGc hGd hG2 hre
    rw [hconj] at hc
    have hn : ‖G (1 - sl y)‖ = ‖G (sl y)‖ := by rw [hc, Complex.norm_conj]
    rw [hL, norm_mul] at hn
    have hGn : 0 < ‖G (sl y)‖ := norm_pos_iff.mpr hG
    nlinarith [norm_nonneg (V (sl y))]
  -- density of the non-zeros of `G` on the line
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  have hG20 : G 2 ≠ 0 := by rw [hG2]; exact bigG_ne_zero lam (by norm_num)
  have hslc : Continuous sl := by rw [hsl_def]; fun_prop
  have hfc : Continuous fun y => ‖V (sl y)‖ := (hVc.comp hslc).norm
  by_contra hne
  have hopen : IsOpen {y : ℝ | ‖V (sl y)‖ ≠ 1} := isOpen_ne_fun hfc continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen y hne
  obtain ⟨z, hz1, hz2, hz0⟩ := exists_ne_zero_mem_Ioo hsl hΦd hΦre hid hGc hGd hG2 hG20 hP hPG
    (a := (y - min δ y / 2) / 2) (b := (y + min δ y / 2) / 2) (by
      have : 0 < min δ y := lt_min hδ hy
      linarith)
  have hvpt : vpt (1 / 2) z = sl (2 * z) := by
    unfold vpt; rw [hsl_def]; push_cast; ring
  rw [hvpt] at hz0
  have hm : 0 < min δ y := lt_min hδ hy
  have hmδ : min δ y ≤ δ := min_le_left _ _
  have hmy : min δ y ≤ y := min_le_right _ _
  have hz2pos : 0 < 2 * z := by linarith
  have hmem : 2 * z ∈ Metric.ball y δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  exact hball hmem (hgood (2 * z) hz2pos hz0)

/-- **Locks whose spectrum has a largest and a smallest frequency force the true producer.** -/
theorem bounded_spectrum_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    {j₁ j₂ : ℕ} (hq₁ : q j₁ ≠ 0) (hq₂ : q j₂ ≠ 0)
    (hext : ∀ j, q j ≠ 0 → ρ j₂ ≤ ρ j ∧ ρ j ≤ ρ j₁)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ) := by
    intro τ hτ
    rw [apLock_of_mem q ρ (le_of_eq (lineS_re τ).symm) (by rw [lineS_re]; norm_num)]
    exact hlock τ hτ
  have hunit := fun {y : ℝ} (hy : 0 < y) => norm_lock_eq_one hsl hΦd hΦre hidT hGc hGd hG2
    (continuous_apLock hρ hq) hlockV hy
  have hqn : Summable fun j => ‖q j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hq
  have hqc : Summable fun j => ‖conj (q j)‖ := by simpa using hqn
  -- the spectrum is a single point
  have hsingle : ρ j₁ = ρ j₂ := by
    by_contra hne
    have hlt : ρ j₂ < ρ j₁ := lt_of_le_of_ne (hext j₁ hq₁).1 (Ne.symm hne)
    set θ : ℝ := Real.log (ρ j₁) - Real.log (ρ j₂) with hθ
    have hθpos : 0 < θ := by
      rw [hθ]; exact sub_pos.mpr (Real.log_lt_log (hρ j₂) hlt)
    -- `|V|² e^{−iθy} − e^{−iθy} = 0` as exponential sums
    have hexp : ∀ y : ℝ, 0 < y →
        (∑' z : ℕ × ℕ, q z.1 * conj (q z.2) *
          cexp (((Real.log (ρ z.1) + -Real.log (ρ z.2) - θ : ℝ) : ℂ) * I * y)) +
        (∑' _u : Unit, (-1 : ℂ) * cexp (((-θ : ℝ) : ℂ) * I * y)) -
          (0 : ℂ) * (∑' _u : Unit, (0 : ℂ) * cexp (((0 : ℝ) : ℂ) * I * y)) = 0 := by
      intro y hy
      have h1 := hunit hy
      rw [apLock_line q hρ y] at h1
      have hsq : (∑' j, q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * y)) *
          conj (∑' j, q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * y)) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num
      rw [conj_tsum_exp] at hsq
      have h' := congrArg (· * cexp (((-θ : ℝ) : ℂ) * I * y)) hsq
      rw [tsum_exp_mul_tsum_exp hqn hqc, one_mul] at h'
      rw [tsum_const, Nat.card_unique, one_smul, tsum_const, Nat.card_unique, one_smul, h']
      ring
    have hrel := mean_coeff_relation (hqn.mul_norm hqc)
      (Summable.of_finite : Summable fun _ : Unit => ‖(-1 : ℂ)‖)
      (Summable.of_finite : Summable fun _ : Unit => ‖(0 : ℂ)‖) _ _ _ 0 hexp
    have hB : (∑' _u : Unit, if -θ = 0 then (-1 : ℂ) else 0) = 0 := by
      rw [if_neg (by linarith)]; simp
    rw [hB, zero_mul, add_zero, sub_zero] at hrel
    -- the extreme coefficient is the only one at frequency `θ`
    have hA : (∑' z : ℕ × ℕ, if Real.log (ρ z.1) + -Real.log (ρ z.2) - θ = 0 then
        q z.1 * conj (q z.2) else 0) = q j₁ * conj (q j₂) := by
      rw [tsum_eq_single (j₁, j₂)]
      · rw [if_pos (by rw [hθ]; ring)]
      · intro z hz
        by_cases hz1 : q z.1 = 0
        · simp [hz1]
        by_cases hz2 : q z.2 = 0
        · simp [hz2]
        rw [if_neg]
        intro h0
        have e1 := hext z.1 hz1
        have e2 := hext z.2 hz2
        have l1 : Real.log (ρ z.1) ≤ Real.log (ρ j₁) := Real.log_le_log (hρ _) e1.2
        have l2 : Real.log (ρ j₂) ≤ Real.log (ρ z.2) := Real.log_le_log (hρ _) e2.1
        have h1 : Real.log (ρ z.1) = Real.log (ρ j₁) := by rw [hθ] at h0; linarith
        have h2 : Real.log (ρ z.2) = Real.log (ρ j₂) := by rw [hθ] at h0; linarith
        have r1 := Real.log_injOn_pos (Set.mem_Ioi.mpr (hρ z.1)) (Set.mem_Ioi.mpr (hρ j₁)) h1
        have r2 := Real.log_injOn_pos (Set.mem_Ioi.mpr (hρ z.2)) (Set.mem_Ioi.mpr (hρ j₂)) h2
        exact hz (Prod.ext (hinj r1) (hinj r2))
    rw [hA] at hrel
    exact mul_ne_zero hq₁ ((map_ne_zero (starRingEnd ℂ)).mpr hq₂) hrel
  -- reduction to a linear lock
  have hsupp : ∀ j, j ≠ j₁ → q j = 0 := by
    intro j hj
    by_contra hqj
    have e := hext j hqj
    have : ρ j = ρ j₁ := le_antisymm e.2 (hsingle ▸ e.1)
    exact hj (hinj this)
  have hlin : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      q j₁ * cexp ((((2 * Real.log (ρ j₁)) * (-τ) : ℝ) : ℂ) * I) *
        cexp ((((0 : ℝ) * (fun _ : ℝ => (0 : ℝ)) (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ
    rw [hlock τ hτ, tsum_eq_single j₁ (fun j hj => by rw [hsupp j hj, zero_mul])]
    have hb : (ρ j₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ j₁).ne'
    rw [Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log (hρ j₁).le, lineS_eq]
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    congr 2
    push_cast; ring
  have hres := linear_twist_rigidity hsl hΦd hΦre hid hGc hGd hG2 (C := fun _ => 0)
    (fun _ _ _ => le_rfl) ⟨0, 0, by norm_num, fun x _ => by simp⟩ hlin
  exact hres.2

/-- **Finite exponential-sum locks force the true producer.** -/
theorem finite_spectrum_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {N : ℕ} {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hfin : ∀ j, N ≤ j → q j = 0)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹ :=
    summable_of_ne_finset_zero (s := Finset.range N) fun j hj => by
      rw [Finset.mem_range, not_lt] at hj; rw [hfin j hj, norm_zero, zero_mul]
  by_cases hex : ∃ j, q j ≠ 0
  · set S : Finset ℕ := (Finset.range N).filter fun j => q j ≠ 0 with hS
    have hSne : S.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj⟩⟩
      by_contra h; exact hj (hfin j (not_lt.mp h))
    obtain ⟨j₁, hj₁S, hj₁⟩ := S.exists_max_image ρ hSne
    obtain ⟨j₂, hj₂S, hj₂⟩ := S.exists_min_image ρ hSne
    have hmemS : ∀ j, q j ≠ 0 → j ∈ S := fun j hj => Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by by_contra h; exact hj (hfin j (not_lt.mp h))), hj⟩
    exact bounded_spectrum_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 hρ hinj hq
      (Finset.mem_filter.mp hj₁S).2 (Finset.mem_filter.mp hj₂S).2
      (fun j hj => ⟨hj₂ j (hmemS j hj), hj₁ j (hmemS j hj)⟩) hlock
  · -- the zero lock is impossible
    push Not at hex
    exfalso
    have hidT : ∀ s : ℂ, 1 < s.re →
        Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
    have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ) := by
      intro τ hτ
      rw [apLock_of_mem q ρ (le_of_eq (lineS_re τ).symm) (by rw [lineS_re]; norm_num)]
      exact hlock τ hτ
    have h1 := norm_lock_eq_one hsl hΦd hΦre hidT hGc hGd hG2 (continuous_apLock hρ hq) hlockV
      (y := 1) one_pos
    rw [apLock_line q hρ 1] at h1
    simp [hex] at h1

end

end AbelianTwist

end RHTower
