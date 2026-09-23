import GaloisForLFunctions.RHTower.ProlateDunsterDensityTransfer

/-!
# The radial mode is bounded on the endpoint interval

The density envelope cannot bound the mode near the regular-singular endpoint: the weight
`1/(pi sqrt((x²-1)(x²-s)))` diverges there.  The bound has to come from the equation itself.

The Sturm form `((t²-1)R')' + c²(t²-s)R = 0` has the natural energy
`E = (t²-1)(R')² + c²(t²-s)R²`, whose derivative is `2t(c²R² - (R')²)`.  That is not sign-definite,
but it is bounded by a fixed multiple of the energy, so Grönwall closes on any short interval.  The
endpoint interval has width `9/(8c²)`, so the exponential factor is at most `exp(1/4)`, and the
normalized initial condition `R 1 = 1` fixes the initial energy exactly.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The Sturm energy of the radial equation at the endpoint. -/
def prolateEndpointEnergy (s c : ℝ) (R DR : ℝ → ℝ) (t : ℝ) : ℝ :=
  (t ^ (2 : ℕ) - 1) * DR t ^ (2 : ℕ) + c ^ (2 : ℕ) * (t ^ (2 : ℕ) - s) * R t ^ (2 : ℕ)

theorem hasDerivAt_prolateEndpointEnergy {s c t : ℝ} {R DR DDR : ℝ → ℝ}
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ (2 : ℕ) - 1) * DDR u + 2 * u * DR u
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * u ^ (2 : ℕ)) * R u = 0) :
    HasDerivAt (prolateEndpointEnergy s c R DR) (2 * t * (c ^ (2 : ℕ) * R t ^ (2 : ℕ) - DR t ^ (2 : ℕ))) t := by
  have hp : HasDerivAt (fun u : ℝ => u ^ (2 : ℕ) - 1) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 1
  have hq : HasDerivAt (fun u : ℝ => c ^ (2 : ℕ) * (u ^ (2 : ℕ) - s)) (c ^ (2 : ℕ) * (2 * t)) t := by
    have h := ((hasDerivAt_pow 2 t).sub_const s).const_mul (c ^ (2 : ℕ))
    simpa using h
  have hd2 : HasDerivAt (fun u : ℝ => DR u ^ (2 : ℕ)) (2 * DR t * DDR t) t := by
    have h := (hDR t).pow 2
    have hv : ((2 : ℕ) : ℝ) * DR t ^ (2 - 1) * DDR t = 2 * DR t * DDR t := by norm_num
    rw [hv] at h
    exact h
  have hr2 : HasDerivAt (fun u : ℝ => R u ^ (2 : ℕ)) (2 * R t * DR t) t := by
    have h := (hR t).pow 2
    have hv : ((2 : ℕ) : ℝ) * R t ^ (2 - 1) * DR t = 2 * R t * DR t := by norm_num
    rw [hv] at h
    exact h
  have hsum := (hp.mul hd2).add (hq.mul hr2)
  have hval : 2 * t * DR t ^ (2 : ℕ) + (t ^ (2 : ℕ) - 1) * (2 * DR t * DDR t)
      + (c ^ (2 : ℕ) * (2 * t) * R t ^ (2 : ℕ) + c ^ (2 : ℕ) * (t ^ (2 : ℕ) - s) * (2 * R t * DR t))
      = 2 * t * (c ^ (2 : ℕ) * R t ^ (2 : ℕ) - DR t ^ (2 : ℕ)) := by
    linear_combination (2 * DR t) * hode t
  rw [← hval]
  exact hsum

theorem prolateEndpointEnergy_nonneg {s c t : ℝ} {R DR : ℝ → ℝ}
    (hs1 : s ≤ 1 / 2) (ht : 1 ≤ t) : 0 ≤ prolateEndpointEnergy s c R DR t := by
  have h1 : (0 : ℝ) ≤ t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) ≤ t ^ (2 : ℕ) - s := by nlinarith
  rw [prolateEndpointEnergy]
  positivity

theorem prolateEndpointEnergy_one {s c : ℝ} {R DR : ℝ → ℝ} (hR1 : R 1 = 1) :
    prolateEndpointEnergy s c R DR 1 = c ^ (2 : ℕ) * (1 - s) := by
  rw [prolateEndpointEnergy, hR1]
  ring

/-- The mode is controlled by the energy, with the endpoint degeneracy already absorbed. -/
theorem sq_le_two_mul_prolateEndpointEnergy {s c t : ℝ} {R DR : ℝ → ℝ}
    (hs1 : s ≤ 1 / 2) (ht : 1 ≤ t) :
    c ^ (2 : ℕ) * R t ^ (2 : ℕ) ≤ 2 * prolateEndpointEnergy s c R DR t := by
  have h1 : (0 : ℝ) ≤ t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (1 : ℝ) / 2 ≤ t ^ (2 : ℕ) - s := by nlinarith
  have hsq : (0 : ℝ) ≤ R t ^ (2 : ℕ) := sq_nonneg _
  have hd : (0 : ℝ) ≤ (t ^ (2 : ℕ) - 1) * DR t ^ (2 : ℕ) := by positivity
  have hmain : c ^ (2 : ℕ) * R t ^ (2 : ℕ) * (1 / 2) ≤ c ^ (2 : ℕ) * R t ^ (2 : ℕ) * (t ^ (2 : ℕ) - s) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [prolateEndpointEnergy]
  nlinarith [hd, hmain]

/-- **Grönwall on the endpoint interval.**  The energy grows at most exponentially, with a fixed
rate, because its derivative is bounded by a fixed multiple of itself. -/
theorem prolateEndpointEnergy_le_exp {s c t : ℝ} {R DR DDR : ℝ → ℝ}
    (hs1 : s ≤ 1 / 2)
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ (2 : ℕ) - 1) * DDR u + 2 * u * DR u
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * u ^ (2 : ℕ)) * R u = 0)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 11 / 10) :
    prolateEndpointEnergy s c R DR t
      ≤ prolateEndpointEnergy s c R DR 1 * Real.exp (5 * (t - 1)) := by
  set F : ℝ → ℝ := prolateEndpointEnergy s c R DR with hFdef
  set G : ℝ → ℝ := fun u : ℝ => F u * Real.exp (-5 * u) with hGdef
  have hFd : ∀ u : ℝ, HasDerivAt F (2 * u * (c ^ (2 : ℕ) * R u ^ (2 : ℕ) - DR u ^ (2 : ℕ))) u :=
    fun u => hasDerivAt_prolateEndpointEnergy hR hDR hode
  have hGd : ∀ u : ℝ, HasDerivAt G
      (2 * u * (c ^ (2 : ℕ) * R u ^ (2 : ℕ) - DR u ^ (2 : ℕ)) * Real.exp (-5 * u)
        + F u * (Real.exp (-5 * u) * -5)) u := by
    intro u
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-5 * v)) (Real.exp (-5 * u) * -5) u := by
      have hin : HasDerivAt (fun v : ℝ => -5 * v) (-5) u := by
        simpa using (hasDerivAt_id u).const_mul (-5 : ℝ)
      simpa using hin.exp
    exact (hFd u).mul hexp
  have hnonpos : ∀ u ∈ Ioo (1 : ℝ) (11 / 10), deriv G u ≤ 0 := by
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu.1
    have hF0 : 0 ≤ F u := prolateEndpointEnergy_nonneg hs1 hu1
    have hsq := sq_le_two_mul_prolateEndpointEnergy (c := c) (R := R) (DR := DR) hs1 hu1
    have hexp0 : 0 < Real.exp (-5 * u) := Real.exp_pos _
    rw [(hGd u).deriv]
    have hkey : 2 * u * (c ^ (2 : ℕ) * R u ^ (2 : ℕ) - DR u ^ (2 : ℕ)) ≤ 5 * F u := by
      nlinarith [hsq, hF0, sq_nonneg (DR u), hu.2, hu1]
    nlinarith [hkey, hexp0, hF0]
  have hcont : ContinuousOn G (Icc 1 (11 / 10)) :=
    fun u _ => ((hGd u).continuousAt).continuousWithinAt
  have hanti : AntitoneOn G (Icc 1 (11 / 10)) := by
    have hdiff : DifferentiableOn ℝ G (interior (Icc (1 : ℝ) (11 / 10))) :=
      fun u _ => ((hGd u).differentiableAt).differentiableWithinAt
    apply antitoneOn_of_deriv_nonpos (convex_Icc 1 (11 / 10)) hcont hdiff
    rw [interior_Icc]
    exact hnonpos
  have hle := hanti (left_mem_Icc.mpr (by norm_num)) ⟨ht1, ht2⟩ ht1
  have hexpt : 0 < Real.exp (-5 * t) := Real.exp_pos _
  rw [hGdef] at hle
  simp only at hle
  have hrewrite : F 1 * Real.exp (-5 * 1)
      = F 1 * Real.exp (5 * (t - 1)) * Real.exp (-5 * t) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hrewrite] at hle
  exact le_of_mul_le_mul_right hle hexpt

/-- **The normalized radial mode is bounded on the endpoint interval.**  The density envelope
diverges there; this bound comes from the equation and the initial condition instead. -/
theorem abs_radialProlate_le_two_endpoint {s c t : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1)
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ (2 : ℕ) - 1) * DDR u + 2 * u * DR u
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * u ^ (2 : ℕ)) * R u = 0)
    (ht1 : 1 ≤ t) (ht2 : t ≤ dunsterEndpointCrossing c) :
    |R t| ≤ 2 := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hA : dunsterEndpointCrossing c ≤ 11 / 10 := dunsterEndpointCrossing_le_eleven_tenths hc
  have ht2' : t ≤ 11 / 10 := le_trans ht2 hA
  have hwidth : t - 1 ≤ 9 / (8 * c ^ (2 : ℕ)) := by
    have := dunsterEndpointCrossing_sub_one (c := c)
    linarith [ht2, this]
  have hrate : 5 * (t - 1) ≤ 1 / 4 := by
    have hc2 : (25 : ℝ) ≤ c ^ (2 : ℕ) := by nlinarith
    have h9 : 9 / (8 * c ^ (2 : ℕ)) ≤ 9 / 200 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hc2]
    linarith [hwidth, h9]
  have hexp2 : Real.exp (5 * (t - 1)) ≤ 2 := by
    have hlog : (1 : ℝ) / 4 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have := Real.exp_lt_exp.mpr (lt_of_le_of_lt hrate hlog)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
    linarith
  have hE := prolateEndpointEnergy_le_exp (R := R) (DR := DR) (DDR := DDR) hs1 hR hDR hode ht1 ht2'
  rw [prolateEndpointEnergy_one hR1] at hE
  have hsq := sq_le_two_mul_prolateEndpointEnergy (c := c) (R := R) (DR := DR) hs1 ht1
  have hE0 : 0 ≤ prolateEndpointEnergy s c R DR t := prolateEndpointEnergy_nonneg hs1 ht1
  have hc2pos : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have hbound : c ^ (2 : ℕ) * R t ^ (2 : ℕ) ≤ 4 * c ^ (2 : ℕ) := by
    have hstep : c ^ (2 : ℕ) * (1 - s) * Real.exp (5 * (t - 1)) ≤ c ^ (2 : ℕ) * 1 * 2 := by
      have h1s : (1 : ℝ) - s ≤ 1 := by linarith
      have hnn : (0 : ℝ) ≤ Real.exp (5 * (t - 1)) := (Real.exp_pos _).le
      calc c ^ (2 : ℕ) * (1 - s) * Real.exp (5 * (t - 1))
          ≤ c ^ (2 : ℕ) * 1 * Real.exp (5 * (t - 1)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1s (le_of_lt hc2pos)) hnn
        _ ≤ c ^ (2 : ℕ) * 1 * 2 := mul_le_mul_of_nonneg_left hexp2 (by positivity)
    nlinarith [hsq, hE, hstep]
  have hR2 : R t ^ (2 : ℕ) ≤ 4 := by
    nlinarith [hbound, hc2pos]
  have : |R t| ^ (2 : ℕ) ≤ 2 ^ (2 : ℕ) := by
    rw [sq_abs]
    linarith
  nlinarith [this, abs_nonneg (R t)]


end GaloisForLFunctions.RHTower
