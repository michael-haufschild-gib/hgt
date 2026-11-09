import GaloisForLFunctions.HyperbolicArakelovTheory.TheImagesOfTheDegreeGeodesic

/-!
# The dilation limit of a twisted carrier

A **twisted carrier** is a family of isometries `γ_i ∈ SL₂(ℂ)` with weights `‖w_i‖ ≤ 1` (a unitary
character of a group, restricted to its non-identity elements, is the model). Its twisted Green sum on
the degree geodesic is

  `F(t, u) = Σ_i w_i · 2πG_{1/2}(d(z_t, γ_i z_u))`   (`carrierSum`, `carrierSum_eq`),

and the question B118′.2 asks whether `F(m, n)` can be the finite part of the Frobenius intersection,
the torsion kernel `Λ(n/m)(n/m)^{−1/2}` (`weilPrimeKernel`). Adding the identity to the family turns
the same question into whether the automorphic Green function carries the whole Frobenius
intersection `2πG_{1/2}(d(z_m, z_n)) + torsion`.

**The endpoint Eisenstein condition** (`EndpointEisenstein`). The degrees `z_n` run to the end `∞` of
the degree geodesic. Put `ω(γ) = ‖c‖⁻¹` if `c ≠ 0` and `ω(γ) = min(‖a‖, ‖a‖⁻¹)` if `c = 0`; the
condition is `Σ_i ω(γ_i) < ∞`. It holds for every carrier whose Poincaré series converges at
`s = ½` and which sees `∞` as a point of discontinuity, i.e. `γ_i(∞)` and `γ_i⁻¹(∞)` stay in a
bounded set, the isometric circles have bounded radii and the stabilizer of `∞` is finite
(`endpointEisenstein_of_poincare`); for a discrete group these are the classical consequences of
`δ(Γ) < ½` and `∞ ∈ Ω(Γ)`.

**The dilation limit** (`tendsto_carrierSum`). Under the condition, along any pairs `(t_k, u_k)` with
`u_k/t_k → r` and `t_k u_k → ∞`,

  `F(t_k, u_k) → L(r) = Σ_{c_i = 0} w_i · 2πG_{1/2}(|log(‖a_i‖² r)|)`   (`dilationLimit`),

for every ratio `r` at which no stabilizer element has `‖a_i‖² r = 1` (`ResonanceFree`). An image with
`c ≠ 0` recedes: `cosh d ≥ ½‖c‖² tu` (`half_mul_le_imageCosh`); an image with `c = 0` acts on the
ratio alone (`imageCosh_of_c_eq_zero`). Dominated convergence with the majorant `C·ω(γ_i)` gives the
limit. So, seen from the end of `ℓ`, every such carrier is a **ratio kernel**: the Manin–Schottky
periodization of the archimedean Green function over the stabilizer of the end.

**No carrier sees the primes** (`not_carrierSum_eq_torsion`). A ratio kernel continuous at `r = p`
cannot jump there, while the torsion kernel jumps at every prime ratio:
`Λ(p)/√p` at `(M, pM)` and `0` at `(M, pM + 1)`. Resonance-free primes exist, because the resonant
primes have `Σ p^{−1/2} < ∞` (`exists_prime_resonanceFree`). Hence no twisted carrier satisfying the
endpoint Eisenstein condition carries the torsion kernel, nor (with the identity added) the whole
Frobenius intersection.

The positive content is the dilation limit itself: hyperbolic carriers realize, at the end of the
degree geodesic, only archimedean (continuous) ratio kernels; the primes must be carried by the
integer structure of `ℙ¹_ℤ`, as the finite part of an Arakelov pairing.
-/

open Filter Topology Set
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-! ## The archimedean profile as a function of `cosh d` -/

/-- `2πG_{1/2}` as a function of `X = cosh d`. -/
def greenOfCosh (X : ℝ) : ℝ := archProfile (Real.arcosh X)

theorem greenOfCosh_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ greenOfCosh X := by
  unfold greenOfCosh
  rcases (Real.arcosh_nonneg hX).eq_or_lt with h | h
  · rw [← h, archProfile_zero]
  · exact (archProfile_pos h).le

/-- Far images: `2πG_{1/2} ≤ (4/3)·X^{−1/2}` for `X = cosh d ≥ 2`. -/
theorem greenOfCosh_le {X : ℝ} (hX : 2 ≤ X) : greenOfCosh X ≤ 4 / 3 * (Real.sqrt X)⁻¹ := by
  unfold greenOfCosh archProfile
  set d := Real.arcosh X
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hE : X ≤ Real.exp d := by
    rw [Real.exp_arcosh hX1]; linarith [Real.sqrt_nonneg (X ^ 2 - 1)]
  have h1 : Real.exp (-d / 2) ≤ (Real.sqrt X)⁻¹ := by
    rw [show -d / 2 = -(d / 2) by ring, Real.exp_neg, Real.exp_half]
    exact inv_anti₀ (Real.sqrt_pos.mpr hXpos) (Real.sqrt_le_sqrt hE)
  have h2 : Real.exp (-2 * d) ≤ 1 / 4 := by
    have he : Real.exp (-2 * d) = (Real.exp d)⁻¹ ^ 2 := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hinv : (Real.exp d)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (Real.exp_pos d) (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num; linarith
    have h0 : 0 ≤ (Real.exp d)⁻¹ := inv_nonneg.mpr (Real.exp_pos d).le
    rw [he]; nlinarith
  calc Real.exp (-d / 2) / (1 - Real.exp (-2 * d)) ≤ (Real.sqrt X)⁻¹ / (3 / 4) :=
        div_le_div₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) h1 (by norm_num) (by linarith)
    _ = 4 / 3 * (Real.sqrt X)⁻¹ := by ring

/-- `2πG_{1/2}` decreases with the distance. -/
theorem greenOfCosh_anti {X Y : ℝ} (hX : 1 < X) (hXY : X ≤ Y) :
    greenOfCosh Y ≤ greenOfCosh X := by
  unfold greenOfCosh
  have h0 : 0 < Real.arcosh X := Real.arcosh_pos hX
  have hle : Real.arcosh X ≤ Real.arcosh Y :=
    (Real.arcosh_le_arcosh (by linarith) (by linarith)).2 hXY
  exact strictAntiOn_archProfile.antitoneOn (mem_Ioi.2 h0) (mem_Ioi.2 (h0.trans_le hle)) hle

theorem continuousAt_archProfile {d : ℝ} (hd : d ≠ 0) : ContinuousAt archProfile d := by
  have h : archProfile = fun d => Real.exp (-d / 2) / (1 - Real.exp (-2 * d)) := rfl
  rw [h]
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (one_sub_exp_neg_two_mul_ne_zero hd)

theorem continuousAt_greenOfCosh {X : ℝ} (hX : 1 < X) : ContinuousAt greenOfCosh X :=
  (continuousAt_archProfile (Real.arcosh_pos hX).ne').comp
    (Real.differentiableAt_arcosh (mem_Ioi.2 hX)).continuousAt

theorem greenOfCosh_half_add_inv {x : ℝ} (hx : 0 < x) :
    greenOfCosh ((x + x⁻¹) / 2) = archProfile |Real.log x| := by
  rw [half_add_inv_eq_cosh hx, greenOfCosh, Real.arcosh_cosh (abs_nonneg _)]

theorem one_lt_half_add_inv {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : 1 < (x + x⁻¹) / 2 := by
  have he : (x + x⁻¹) / 2 - 1 = (x - 1) ^ 2 / (2 * x) := by field_simp; ring
  have hsq : 0 < (x - 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hx1)))
  have hpos : 0 < (x - 1) ^ 2 / (2 * x) := div_pos hsq (by positivity)
  linarith

/-- `(√X)⁻¹ ≤ K` as soon as `K⁻² ≤ X`. -/
theorem inv_sqrt_le_of_le {K X : ℝ} (hK : 0 < K) (h : K⁻¹ ^ 2 ≤ X) : (Real.sqrt X)⁻¹ ≤ K := by
  have h1 : K⁻¹ ≤ Real.sqrt X := by
    rw [← Real.sqrt_sq (inv_nonneg.mpr hK.le)]; exact Real.sqrt_le_sqrt h
  calc (Real.sqrt X)⁻¹ ≤ (K⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hK) h1
    _ = K := inv_inv K

/-! ## Carriers -/

/-- The twisted Green sum `Σ_i w_i·2πG_{1/2}(d(z_t, γ_i z_u))` of a carrier. -/
def carrierSum {ι : Type*} (γ : ι → SL2C) (w : ι → ℂ) (t u : ℝ) : ℂ :=
  ∑' i, w i * (greenOfCosh (imageCosh (γ i) t u) : ℂ)

theorem carrierSum_eq {ι : Type*} (γ : ι → SL2C) (w : ι → ℂ) {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) :
    carrierSum γ w t u =
      ∑' i, w i * (archProfile (h3Dist (degPoint t ht) (h3Act (γ i) (degPoint u hu))) : ℂ) := by
  simp only [carrierSum, greenOfCosh, h3Dist_degPoint_h3Act]

/-- The endpoint weight `ω(γ)`: `‖c‖⁻¹` off the stabilizer of `∞`, `min(‖a‖, ‖a‖⁻¹)` on it. -/
def endWeight (g : SL2C) : ℝ :=
  if g.1 1 0 = 0 then min ‖g.1 0 0‖ ‖g.1 0 0‖⁻¹ else ‖g.1 1 0‖⁻¹

theorem endWeight_nonneg (g : SL2C) : 0 ≤ endWeight g := by
  unfold endWeight
  split_ifs
  · exact le_min (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))
  · exact inv_nonneg.mpr (norm_nonneg _)

/-- **The endpoint Eisenstein condition**: `Σ_i ω(γ_i) < ∞`. -/
def EndpointEisenstein {ι : Type*} (γ : ι → SL2C) : Prop :=
  Summable fun i => endWeight (γ i)

/-- No stabilizer element of `∞` translates the degree geodesic by `−log r`. -/
def ResonanceFree {ι : Type*} (γ : ι → SL2C) (r : ℝ) : Prop :=
  ∀ i, (γ i).1 1 0 = 0 → ‖(γ i).1 0 0‖ ^ 2 * r ≠ 1

/-- The dilation limit `L(r) = Σ_{c_i = 0} w_i·2πG_{1/2}(|log(‖a_i‖² r)|)`. -/
def dilationLimit {ι : Type*} (γ : ι → SL2C) (w : ι → ℂ) (r : ℝ) : ℂ :=
  ∑' i, if (γ i).1 1 0 = 0 then w i * (archProfile |Real.log (‖(γ i).1 0 0‖ ^ 2 * r)| : ℂ) else 0

/-! ## The limit of one image -/

theorem tendsto_greenOfCosh_imageCosh {g : SL2C} {r : ℝ} (hr : 0 < r)
    (hres : g.1 1 0 = 0 → ‖g.1 0 0‖ ^ 2 * r ≠ 1) {t u : ℕ → ℝ} (ht : ∀ k, 0 < t k)
    (hu : ∀ k, 0 < u k) (hratio : Tendsto (fun k => u k / t k) atTop (𝓝 r))
    (hprod : Tendsto (fun k => t k * u k) atTop atTop) :
    Tendsto (fun k => greenOfCosh (imageCosh g (t k) (u k))) atTop
      (𝓝 (if g.1 1 0 = 0 then archProfile |Real.log (‖g.1 0 0‖ ^ 2 * r)| else 0)) := by
  by_cases hc : g.1 1 0 = 0
  · rw [if_pos hc]
    obtain ⟨ha, -⟩ := norm_d_of_c_eq_zero hc
    have hx : 0 < ‖g.1 0 0‖ ^ 2 * r := mul_pos (pow_pos (norm_pos_iff.mpr ha) 2) hr
    have hx1 := hres hc
    have hxk : Tendsto (fun k => ‖g.1 0 0‖ ^ 2 * (u k / t k)) atTop
        (𝓝 (‖g.1 0 0‖ ^ 2 * r)) := hratio.const_mul _
    have hb : Tendsto (fun k => ‖g.1 0 1‖ ^ 2 * (t k * u k)⁻¹ / 2) atTop (𝓝 0) := by
      have := ((tendsto_inv_atTop_zero.comp hprod).const_mul (‖g.1 0 1‖ ^ 2)).div_const 2
      simpa using this
    have hX : Tendsto (fun k => imageCosh g (t k) (u k)) atTop
        (𝓝 ((‖g.1 0 0‖ ^ 2 * r + (‖g.1 0 0‖ ^ 2 * r)⁻¹) / 2)) := by
      have h1 := ((hxk.add (hxk.inv₀ hx.ne')).div_const 2).add hb
      rw [add_zero] at h1
      refine h1.congr' (Eventually.of_forall fun k => ?_)
      simp only [imageCosh_of_c_eq_zero hc (ht k) (hu k)]
    rw [← greenOfCosh_half_add_inv hx]
    exact (continuousAt_greenOfCosh (one_lt_half_add_inv hx hx1)).tendsto.comp hX
  · rw [if_neg hc]
    have hc0 : 0 < ‖g.1 1 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hc) 2
    have hX : Tendsto (fun k => imageCosh g (t k) (u k)) atTop atTop :=
      tendsto_atTop_mono (fun k => half_mul_le_imageCosh g (ht k) (hu k))
        ((hprod.const_mul_atTop hc0).atTop_div_const two_pos)
    have hup : Tendsto (fun k => 4 / 3 * (Real.sqrt (imageCosh g (t k) (u k)))⁻¹) atTop
        (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hX)).const_mul (4 / 3)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · exact Eventually.of_forall fun k => greenOfCosh_nonneg (one_le_imageCosh g (ht k) (hu k))
    · filter_upwards [hX.eventually_ge_atTop 2] with k hk
      exact greenOfCosh_le hk

/-! ## The uniform bound away from a finite set -/

/-- Off a finite set, `2πG_{1/2}(d(z_t, γz_u)) ≤ C(r)·ω(γ)` once `tu ≥ 4` and `u/t ∈ [r/2, 2r]`. -/
theorem greenOfCosh_imageCosh_le_endWeight {g : SL2C} {r t u : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hu : 0 < u) (hP : 4 ≤ t * u) (hr1 : r / 2 ≤ u / t) (hr2 : u / t ≤ 2 * r)
    (hsmall : endWeight g < min 1 (min (Real.sqrt r / 3) ((Real.sqrt r)⁻¹ / 3))) :
    greenOfCosh (imageCosh g t u) ≤
      4 / 3 * (1 + 2 * (Real.sqrt r)⁻¹ + 2 * Real.sqrt r) * endWeight g := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hsri : 0 < (Real.sqrt r)⁻¹ := inv_pos.mpr hsr
  have hw0 := endWeight_nonneg g
  have hsm1 : endWeight g < 1 := hsmall.trans_le (min_le_left _ _)
  have hsm2 : endWeight g < Real.sqrt r / 3 :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsm3 : endWeight g < (Real.sqrt r)⁻¹ / 3 :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hc : g.1 1 0 = 0
  · obtain ⟨ha, -⟩ := norm_d_of_c_eq_zero hc
    have hapos : 0 < ‖g.1 0 0‖ := norm_pos_iff.mpr ha
    have hX := imageCosh_of_c_eq_zero hc ht hu
    set x := ‖g.1 0 0‖ ^ 2 * (u / t) with hxdef
    have hxpos : 0 < x := by positivity
    have hb : 0 ≤ ‖g.1 0 1‖ ^ 2 * (t * u)⁻¹ / 2 := by positivity
    have hwe : endWeight g = min ‖g.1 0 0‖ ‖g.1 0 0‖⁻¹ := by simp [endWeight, hc]
    rcases le_or_gt ‖g.1 0 0‖ 1 with ha1 | ha1
    · -- small multiplier: the inverse ratio term dominates
      have hmin : endWeight g = ‖g.1 0 0‖ := by
        rw [hwe]; exact min_eq_left (ha1.trans (one_le_inv₀ hapos |>.mpr ha1))
      have hsmall' : ‖g.1 0 0‖ * Real.sqrt r < 1 / 3 := by
        rw [← hmin]
        have := mul_lt_mul_of_pos_right hsm3 hsr
        rwa [div_mul_eq_mul_div, inv_mul_cancel₀ hsr.ne'] at this
      have ha2 : ‖g.1 0 0‖ ^ 2 * r < 1 / 9 := by
        have : (‖g.1 0 0‖ * Real.sqrt r) ^ 2 < (1 / 3) ^ 2 :=
          pow_lt_pow_left₀ hsmall' (by positivity) two_ne_zero
        rw [mul_pow, hsq] at this; linarith
      have hxle : x ≤ 2 * r * ‖g.1 0 0‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hr2 (sq_nonneg ‖g.1 0 0‖)
        rw [hxdef]; linarith
      have hxinv : (4 * r * ‖g.1 0 0‖ ^ 2)⁻¹ ≤ x⁻¹ / 2 := by
        rw [show x⁻¹ / 2 = (2 * x)⁻¹ by ring]
        exact inv_anti₀ (by positivity) (by linarith)
      have hXge : (4 * r * ‖g.1 0 0‖ ^ 2)⁻¹ ≤ imageCosh g t u := by
        rw [hX]; linarith [hxinv, hxpos.le]
      have h2 : 2 ≤ imageCosh g t u := by
        refine le_trans ?_ hXge
        rw [le_inv_comm₀ (by norm_num) (by positivity)]; norm_num; nlinarith
      have hK : 0 < 2 * Real.sqrt r * ‖g.1 0 0‖ := by positivity
      have hsq' : (2 * Real.sqrt r * ‖g.1 0 0‖)⁻¹ ^ 2 ≤ imageCosh g t u := by
        have e : (2 * Real.sqrt r * ‖g.1 0 0‖)⁻¹ ^ 2 =
            (4 * Real.sqrt r ^ 2 * ‖g.1 0 0‖ ^ 2)⁻¹ := by
          field_simp; ring
        rw [e, hsq]; exact hXge
      calc greenOfCosh (imageCosh g t u) ≤ 4 / 3 * (Real.sqrt (imageCosh g t u))⁻¹ :=
            greenOfCosh_le h2
        _ ≤ 4 / 3 * (2 * Real.sqrt r * ‖g.1 0 0‖) := by
            gcongr; exact inv_sqrt_le_of_le hK hsq'
        _ ≤ 4 / 3 * (1 + 2 * (Real.sqrt r)⁻¹ + 2 * Real.sqrt r) * endWeight g := by
            rw [hmin]; nlinarith [mul_pos hsri hapos]
    · -- large multiplier: the ratio term dominates
      have hmin : endWeight g = ‖g.1 0 0‖⁻¹ := by
        rw [hwe]; exact min_eq_right ((inv_lt_one_of_one_lt₀ ha1).le.trans ha1.le)
      have hbig : 3 < ‖g.1 0 0‖ * Real.sqrt r := by
        rw [hmin] at hsm2
        have h := mul_lt_mul_of_pos_left hsm2 hapos
        rw [mul_inv_cancel₀ hapos.ne'] at h; linarith
      have ha2 : 9 < ‖g.1 0 0‖ ^ 2 * r := by
        have : (3 : ℝ) ^ 2 < (‖g.1 0 0‖ * Real.sqrt r) ^ 2 :=
          pow_lt_pow_left₀ hbig (by norm_num) two_ne_zero
        rw [mul_pow, hsq] at this; linarith
      have hxge : ‖g.1 0 0‖ ^ 2 * r / 2 ≤ x := by
        have := mul_le_mul_of_nonneg_left hr1 (sq_nonneg ‖g.1 0 0‖)
        rw [hxdef]; linarith
      have hXge : ‖g.1 0 0‖ ^ 2 * r / 4 ≤ imageCosh g t u := by
        have := inv_pos.mpr hxpos
        rw [hX]; linarith
      have h2 : 2 ≤ imageCosh g t u := by linarith
      have hK : 0 < 2 * (Real.sqrt r)⁻¹ * ‖g.1 0 0‖⁻¹ := by positivity
      have hsq' : (2 * (Real.sqrt r)⁻¹ * ‖g.1 0 0‖⁻¹)⁻¹ ^ 2 ≤ imageCosh g t u := by
        have e : (2 * (Real.sqrt r)⁻¹ * ‖g.1 0 0‖⁻¹)⁻¹ ^ 2 =
            ‖g.1 0 0‖ ^ 2 * Real.sqrt r ^ 2 / 4 := by
          field_simp; ring
        rw [e, hsq]; exact hXge
      calc greenOfCosh (imageCosh g t u) ≤ 4 / 3 * (Real.sqrt (imageCosh g t u))⁻¹ :=
            greenOfCosh_le h2
        _ ≤ 4 / 3 * (2 * (Real.sqrt r)⁻¹ * ‖g.1 0 0‖⁻¹) := by
            gcongr; exact inv_sqrt_le_of_le hK hsq'
        _ ≤ 4 / 3 * (1 + 2 * (Real.sqrt r)⁻¹ + 2 * Real.sqrt r) * endWeight g := by
            rw [hmin]; nlinarith [mul_pos hsr (inv_pos.mpr hapos)]
  · have hwe : endWeight g = ‖g.1 1 0‖⁻¹ := by simp [endWeight, hc]
    have hcpos : 0 < ‖g.1 1 0‖ := norm_pos_iff.mpr hc
    have hc1 : 1 < ‖g.1 1 0‖ := by
      rw [hwe] at hsm1; exact (inv_lt_one₀ hcpos).mp hsm1
    have hXge : ‖g.1 1 0‖ ^ 2 ≤ imageCosh g t u := by
      have := half_mul_le_imageCosh g ht hu
      nlinarith [sq_nonneg ‖g.1 1 0‖]
    have h2 : 2 ≤ imageCosh g t u := by
      have := half_mul_le_imageCosh g ht hu
      nlinarith
    have hsq' : (‖g.1 1 0‖⁻¹)⁻¹ ^ 2 ≤ imageCosh g t u := by rwa [inv_inv]
    calc greenOfCosh (imageCosh g t u) ≤ 4 / 3 * (Real.sqrt (imageCosh g t u))⁻¹ :=
          greenOfCosh_le h2
      _ ≤ 4 / 3 * ‖g.1 1 0‖⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_sqrt_le_of_le (inv_pos.mpr hcpos) hsq') (by norm_num)
      _ ≤ 4 / 3 * (1 + 2 * (Real.sqrt r)⁻¹ + 2 * Real.sqrt r) * endWeight g := by
          rw [hwe]
          have : 0 ≤ ‖g.1 1 0‖⁻¹ := inv_nonneg.mpr hcpos.le
          nlinarith [mul_nonneg hsri.le this, mul_nonneg hsr.le this]

theorem norm_carrierTerm_le {w : ℂ} (hw : ‖w‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖w * (greenOfCosh X : ℂ)‖ ≤ greenOfCosh X := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (greenOfCosh_nonneg hX)]
  exact mul_le_of_le_one_left (greenOfCosh_nonneg hX) hw

/-! ## The dilation limit -/

/-- **The dilation limit of a twisted carrier.** Under the endpoint Eisenstein condition, along
pairs with `u_k/t_k → r` and `t_k u_k → ∞`, `F(t_k, u_k) → L(r)`. -/
theorem tendsto_carrierSum {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ} (hE : EndpointEisenstein γ)
    (hw : ∀ i, ‖w i‖ ≤ 1) {r : ℝ} (hr : 0 < r) (hres : ResonanceFree γ r) {t u : ℕ → ℝ}
    (ht : ∀ k, 0 < t k) (hu : ∀ k, 0 < u k) (hratio : Tendsto (fun k => u k / t k) atTop (𝓝 r))
    (hprod : Tendsto (fun k => t k * u k) atTop atTop) :
    Tendsto (fun k => carrierSum γ w (t k) (u k)) atTop (𝓝 (dilationLimit γ w r)) := by
  unfold carrierSum
  set L : ι → ℝ := fun i =>
    if (γ i).1 1 0 = 0 then archProfile |Real.log (‖(γ i).1 0 0‖ ^ 2 * r)| else 0 with hL
  have hterm : ∀ i, Tendsto (fun k => w i * (greenOfCosh (imageCosh (γ i) (t k) (u k)) : ℂ))
      atTop (𝓝 (w i * (L i : ℂ))) := fun i =>
    ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_greenOfCosh_imageCosh hr (hres i) ht hu hratio hprod)).const_mul (w i)
  have hlim : dilationLimit γ w r = ∑' i, w i * (L i : ℂ) := by
    unfold dilationLimit
    congr 1; funext i
    simp only [hL]
    split_ifs <;> simp
  rw [hlim]
  set τ := min 1 (min (Real.sqrt r / 3) ((Real.sqrt r)⁻¹ / 3)) with hτdef
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hτ : 0 < τ := by positivity
  have hF : Set.Finite {i | τ ≤ endWeight (γ i)} := by
    have h2 := hE.tendsto_cofinite_zero.eventually (gt_mem_nhds hτ)
    simpa [Filter.eventually_cofinite, not_lt] using h2
  set C := 4 / 3 * (1 + 2 * (Real.sqrt r)⁻¹ + 2 * Real.sqrt r) with hC
  have hC0 : 0 ≤ C := by positivity
  set E : ι → ℝ := fun i => if τ ≤ endWeight (γ i) then |L i| + 1 else 0 with hEdef
  have hEsum : Summable E := by
    refine summable_of_ne_finset_zero (s := hF.toFinset) fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, mem_setOf_eq] at hi
    simp [hEdef, hi]
  refine tendsto_tsum_of_dominated_convergence
    (f := fun k i => w i * (greenOfCosh (imageCosh (γ i) (t k) (u k)) : ℂ))
    (bound := fun i => C * endWeight (γ i) + E i) ((hE.mul_left C).add hEsum) hterm ?_
  have hev1 : ∀ᶠ k in atTop, ∀ i ∈ {i | τ ≤ endWeight (γ i)},
      ‖w i * (greenOfCosh (imageCosh (γ i) (t k) (u k)) : ℂ)‖ ≤ |L i| + 1 := by
    rw [eventually_all_finite hF]
    intro i _
    have hn := (hterm i).norm
    have hle : ‖w i * (L i : ℂ)‖ ≤ |L i| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (hw i)
    filter_upwards [hn.eventually (gt_mem_nhds (lt_add_one ‖w i * (L i : ℂ)‖))] with k hk
    linarith
  have hev2 : ∀ᶠ k in atTop, 4 ≤ t k * u k ∧ u k / t k ∈ Icc (r / 2) (2 * r) :=
    (hprod.eventually_ge_atTop 4).and
      (hratio.eventually (Icc_mem_nhds (by linarith) (by linarith)))
  filter_upwards [hev1, hev2] with k h1 h2 i
  obtain ⟨hP, hr1, hr2⟩ := h2
  have hwnn : 0 ≤ C * endWeight (γ i) := mul_nonneg hC0 (endWeight_nonneg _)
  by_cases hi : τ ≤ endWeight (γ i)
  · have := h1 i hi
    have hEi : E i = |L i| + 1 := by simp [hEdef, hi]
    rw [hEi]; linarith
  · push Not at hi
    have hEi : E i = 0 := by simp [hEdef, not_le.mpr hi]
    rw [hEi, add_zero]
    exact (norm_carrierTerm_le (hw i) (one_le_imageCosh _ (ht k) (hu k))).trans
      (greenOfCosh_imageCosh_le_endWeight hr (ht k) (hu k) hP hr1 hr2 hi)

/-! ## The jump at a prime ratio -/

theorem tendsto_natCast_add_one_atTop :
    Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- **A carrier cannot jump at a resonance-free ratio.** -/
theorem tendsto_carrierSum_sub {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ} (hE : EndpointEisenstein γ)
    (hw : ∀ i, ‖w i‖ ≤ 1) {p : ℝ} (hp : 1 ≤ p) (hres : ResonanceFree γ p) :
    Tendsto (fun M : ℕ => carrierSum γ w ((M : ℝ) + 1) (p * ((M : ℝ) + 1)) -
      carrierSum γ w ((M : ℝ) + 1) (p * ((M : ℝ) + 1) + 1)) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have ht : ∀ M : ℕ, 0 < (M : ℝ) + 1 := fun M => by positivity
  have hprod1 : Tendsto (fun M : ℕ => ((M : ℝ) + 1) * (p * ((M : ℝ) + 1))) atTop atTop := by
    refine tendsto_atTop_mono (fun M => ?_) tendsto_natCast_add_one_atTop
    have h1 : (1 : ℝ) ≤ p * ((M : ℝ) + 1) := by nlinarith [ht M]
    nlinarith [ht M]
  have hprod2 : Tendsto (fun M : ℕ => ((M : ℝ) + 1) * (p * ((M : ℝ) + 1) + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun M => ?_) tendsto_natCast_add_one_atTop
    nlinarith [ht M, mul_nonneg (ht M).le (mul_nonneg hp0.le (ht M).le)]
  have hrat1 : Tendsto (fun M : ℕ => p * ((M : ℝ) + 1) / ((M : ℝ) + 1)) atTop (𝓝 p) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun M =>
      (mul_div_cancel_right₀ p (ht M).ne').symm)
  have hrat2 : Tendsto (fun M : ℕ => (p * ((M : ℝ) + 1) + 1) / ((M : ℝ) + 1)) atTop (𝓝 p) := by
    have h : Tendsto (fun M : ℕ => p + ((M : ℝ) + 1)⁻¹) atTop (𝓝 (p + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_add_one_atTop)
    rw [add_zero] at h
    refine h.congr' (Eventually.of_forall fun M => ?_)
    field_simp [(ht M).ne']
  have h1 := tendsto_carrierSum hE hw hp0 hres (t := fun M : ℕ => (M : ℝ) + 1)
    (u := fun M : ℕ => p * ((M : ℝ) + 1)) ht (fun M => mul_pos hp0 (ht M)) hrat1 hprod1
  have h2 := tendsto_carrierSum hE hw hp0 hres (t := fun M : ℕ => (M : ℝ) + 1)
    (u := fun M : ℕ => p * ((M : ℝ) + 1) + 1) ht
    (fun M => by have := mul_pos hp0 (ht M); linarith) hrat2 hprod2
  simpa using h1.sub h2

/-! ## Resonance-free primes exist -/

/-- The resonant primes `p` (some stabilizer element has `‖a‖² p = 1`) have `Σ p^{−1/2} < ∞`;
since `Σ_p p^{−1/2} = ∞`, some prime is resonance-free. -/
theorem exists_prime_resonanceFree {ι : Type*} {γ : ι → SL2C} (hE : EndpointEisenstein γ) :
    ∃ p : ℕ, p.Prime ∧ ResonanceFree γ p := by
  by_contra hcon
  push Not at hcon
  have hbad : ∀ p : Nat.Primes, ∃ i, (γ i).1 1 0 = 0 ∧ ‖(γ i).1 0 0‖ ^ 2 * ((p : ℕ) : ℝ) = 1 := by
    intro p
    have h := hcon p p.2
    simp only [ResonanceFree, not_forall, not_not] at h
    obtain ⟨i, hc, hi⟩ := h
    exact ⟨i, hc, hi⟩
  choose φ hφc hφ using hbad
  have hinj : Function.Injective φ := by
    intro p q hpq
    have h1 := hφ p
    have h2 := hφ q
    rw [hpq] at h1
    have ha := (norm_d_of_c_eq_zero (hφc q)).1
    have hpos : 0 < ‖(γ (φ q)).1 0 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
    have hpq' : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by
      have := h1.trans h2.symm
      exact mul_left_cancel₀ hpos.ne' this
    exact Subtype.ext (by exact_mod_cast hpq')
  have hval : ∀ p : Nat.Primes, endWeight (γ (φ p)) = ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p
    have ha := (norm_d_of_c_eq_zero (hφc p)).1
    have hapos : 0 < ‖(γ (φ p)).1 0 0‖ := norm_pos_iff.mpr ha
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hsq : ‖(γ (φ p)).1 0 0‖ ^ 2 = ((p : ℕ) : ℝ)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (hφ p)
    have hnorm : ‖(γ (φ p)).1 0 0‖ = (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
      rw [← Real.sqrt_inv, ← hsq, Real.sqrt_sq hapos.le]
    have hle1 : ‖(γ (φ p)).1 0 0‖ ≤ 1 := by
      have : ‖(γ (φ p)).1 0 0‖ ^ 2 ≤ 1 := by
        rw [hsq]; exact inv_le_one_of_one_le₀ (by linarith)
      nlinarith [hapos]
    simp only [endWeight, hφc p, if_true]
    rw [min_eq_left (hle1.trans ((one_le_inv₀ hapos).mpr hle1)), hnorm,
      Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  have hs : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (hE.comp_injective hinj).congr fun p => hval p
  have := Nat.Primes.summable_rpow.1 hs
  norm_num at this

/-! ## No twisted carrier sees the primes -/

theorem weilPrimeKernel_mul_prime {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    weilPrimeKernel m (p * m) = Real.log p / Real.sqrt p := by
  have hne : m ≠ p * m := by
    intro h
    have : 1 * m = p * m := by rw [one_mul]; exact h
    exact hp.one_lt.ne (Nat.eq_of_mul_eq_mul_right hm this)
  rw [weilPrimeKernel, if_pos ⟨dvd_mul_left m p, hne⟩, Nat.mul_div_cancel _ hm,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem weilPrimeKernel_mul_prime_add_one {p m : ℕ} (hp : 1 ≤ p) (hm : 2 ≤ m) :
    weilPrimeKernel m (p * m + 1) = 0 := by
  have h1 : ¬ (m ∣ p * m + 1 ∧ m ≠ p * m + 1) := by
    rintro ⟨h, -⟩
    have := (Nat.dvd_add_right (dvd_mul_left m p)).1 h
    have := Nat.le_of_dvd one_pos this
    omega
  have h2 : ¬ (p * m + 1 ∣ m ∧ p * m + 1 ≠ m) := by
    rintro ⟨h, -⟩
    have := Nat.le_of_dvd (by omega) h
    nlinarith
  rw [weilPrimeKernel, if_neg h1, if_neg h2]

/-- **No twisted carrier with the endpoint Eisenstein condition carries the torsion kernel**
(B118′.2): for every nonzero normalization `κ`, `F(m, n) = κ·Λ(n/m)(n/m)^{−1/2}` fails at some pair
of distinct degrees. -/
theorem not_carrierSum_eq_torsion {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ}
    (hE : EndpointEisenstein γ) (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum γ w m n = κ * (weilPrimeKernel m n : ℂ) := by
  intro h
  obtain ⟨p, hp, hres⟩ := exists_prime_resonanceFree hE
  have hlim := tendsto_carrierSum_sub hE hw (p := p) (by exact_mod_cast hp.one_lt.le) hres
  have hconst : ∀ M : ℕ, 1 ≤ M →
      carrierSum γ w ((M : ℝ) + 1) (p * ((M : ℝ) + 1)) -
        carrierSum γ w ((M : ℝ) + 1) (p * ((M : ℝ) + 1) + 1) =
      κ * ((Real.log p / Real.sqrt p : ℝ) : ℂ) := by
    intro M hM
    have hm : 2 ≤ M + 1 := by omega
    have e1 := h (M + 1) (p * (M + 1)) (by omega) (Nat.mul_pos hp.pos (by omega))
      (by intro h'; nlinarith [hp.two_le])
    have e2 := h (M + 1) (p * (M + 1) + 1) (by omega) (by omega)
      (by intro h'; nlinarith [hp.two_le])
    push_cast at e1 e2
    rw [e1, e2, weilPrimeKernel_mul_prime hp (by omega),
      weilPrimeKernel_mul_prime_add_one hp.one_lt.le hm]
    push_cast; ring
  have hlim' : Tendsto (fun _ : ℕ => κ * ((Real.log p / Real.sqrt p : ℝ) : ℂ)) atTop (𝓝 0) :=
    hlim.congr' ((eventually_ge_atTop 1).mono fun M hM => hconst M hM)
  have h0 := tendsto_nhds_unique tendsto_const_nhds hlim'
  have hpos : 0 < Real.log p / Real.sqrt p :=
    div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos))
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact hκ h'
  · exact hpos.ne' (by exact_mod_cast h')

/-! ## The Eisenstein condition from the Poincaré series -/

/-- **Poincaré convergence at `s = ½` plus discontinuity at `∞` give the Eisenstein condition.**
If `Σ_i e^{−d(z_1, γ_i z_1)/2} < ∞`, every `γ_i` with `c_i ≠ 0` has `‖a_i‖, ‖d_i‖ ≤ R‖c_i‖` and
`‖c_i‖ ≥ 1/R` (bounded `γ_i^{±1}(∞)`, bounded isometric radii), and only finitely many `γ_i` fix `∞`,
then `Σ_i ω(γ_i) < ∞`. -/
theorem endpointEisenstein_of_poincare {ι : Type*} {γ : ι → SL2C} {R : ℝ} (hR : 0 < R)
    (hP : Summable fun i =>
      Real.exp (-(h3Dist (degPoint 1 one_pos) (h3Act (γ i) (degPoint 1 one_pos))) / 2))
    (horb : ∀ i, (γ i).1 1 0 ≠ 0 → ‖(γ i).1 0 0‖ ≤ R * ‖(γ i).1 1 0‖ ∧
      ‖(γ i).1 1 1‖ ≤ R * ‖(γ i).1 1 0‖ ∧ 1 ≤ R * ‖(γ i).1 1 0‖)
    (hstab : {i | (γ i).1 1 0 = 0}.Finite) : EndpointEisenstein γ := by
  set K := Real.sqrt (2 * (2 * R ^ 2 + 4 * R ^ 4 + 1)) with hK
  set S : ι → ℝ := fun i => if (γ i).1 1 0 = 0 then endWeight (γ i) else 0 with hS
  have hSsum : Summable S := by
    refine summable_of_ne_finset_zero (s := hstab.toFinset) fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, mem_setOf_eq] at hi
    simp [hS, hi]
  refine Summable.of_nonneg_of_le (fun i => endWeight_nonneg _) (fun i => ?_)
    ((hP.mul_left K).add hSsum)
  by_cases hc : (γ i).1 1 0 = 0
  · have : S i = endWeight (γ i) := by simp [hS, hc]
    rw [this]
    have he := Real.exp_nonneg (-(h3Dist (degPoint 1 one_pos) (h3Act (γ i) (degPoint 1 one_pos))) / 2)
    have hK0 : 0 ≤ K := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hK0 he]
  · have hS0 : S i = 0 := by simp [hS, hc]
    rw [hS0, add_zero]
    have hwe : endWeight (γ i) = ‖(γ i).1 1 0‖⁻¹ := by simp [endWeight, hc]
    obtain ⟨ha, hd, hc1⟩ := horb i hc
    set a := (γ i).1 0 0
    set b := (γ i).1 0 1
    set c := (γ i).1 1 0
    set d := (γ i).1 1 1
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hdet : a * d - b * c = 1 := by
      have := (γ i).prop
      rwa [Matrix.det_fin_two] at this
    -- `‖b‖ ≤ 2R²‖c‖`
    have hb : ‖b‖ ≤ 2 * R ^ 2 * ‖c‖ := by
      have hbc : ‖b‖ * ‖c‖ ≤ ‖a‖ * ‖d‖ + 1 := by
        rw [← norm_mul, show b * c = a * d - 1 by linear_combination -hdet]
        calc ‖a * d - 1‖ ≤ ‖a * d‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖a‖ * ‖d‖ + 1 := by rw [norm_mul, norm_one]
      have had : ‖a‖ * ‖d‖ ≤ R ^ 2 * ‖c‖ ^ 2 := by
        calc ‖a‖ * ‖d‖ ≤ (R * ‖c‖) * (R * ‖c‖) :=
              mul_le_mul ha hd (norm_nonneg _) (by positivity)
          _ = R ^ 2 * ‖c‖ ^ 2 := by ring
      have h1 : 1 ≤ R ^ 2 * ‖c‖ ^ 2 := by nlinarith
      have : ‖b‖ * ‖c‖ ≤ 2 * R ^ 2 * ‖c‖ * ‖c‖ := by nlinarith
      exact le_of_mul_le_mul_right this hcpos
    -- `2 cosh d(z_1, γz_1) ≤ (2R² + 4R⁴ + 1)·‖c‖²`
    have hX : 2 * imageCosh (γ i) 1 1 ≤ (2 * R ^ 2 + 4 * R ^ 4 + 1) * ‖c‖ ^ 2 := by
      have he : 2 * imageCosh (γ i) 1 1 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
        simp only [imageCosh]; ring
      rw [he]
      have h1 : ‖a‖ ^ 2 ≤ R ^ 2 * ‖c‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg _) ha; nlinarith
      have h2 : ‖d‖ ^ 2 ≤ R ^ 2 * ‖c‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg _) hd; nlinarith
      have h3 : ‖b‖ ^ 2 ≤ 4 * R ^ 4 * ‖c‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg _) hb; nlinarith
      nlinarith
    -- `e^{−d/2} ≥ (2 cosh d)^{−1/2}`
    have hdist := h3Dist_degPoint_h3Act (γ i) (one_pos : (0 : ℝ) < 1) one_pos
    have hX1 := one_le_imageCosh (γ i) (one_pos : (0 : ℝ) < 1) one_pos
    have hexp : (Real.sqrt (2 * imageCosh (γ i) 1 1))⁻¹ ≤
        Real.exp (-(h3Dist (degPoint 1 one_pos) (h3Act (γ i) (degPoint 1 one_pos))) / 2) := by
      rw [hdist, show -Real.arcosh (imageCosh (γ i) 1 1) / 2 =
          -(Real.arcosh (imageCosh (γ i) 1 1) / 2) by ring, Real.exp_neg, Real.exp_half,
        Real.exp_arcosh hX1]
      have hs0 := Real.sqrt_nonneg (imageCosh (γ i) 1 1 ^ 2 - 1)
      refine inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt ?_)
      have h3 : Real.sqrt (imageCosh (γ i) 1 1 ^ 2 - 1) ≤ Real.sqrt (imageCosh (γ i) 1 1 ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_sq (by linarith)] at h3
      linarith
    have hKpos : 0 < K := Real.sqrt_pos.mpr (by positivity)
    rw [hwe]
    have hsqle : Real.sqrt (2 * imageCosh (γ i) 1 1) ≤ K * ‖c‖ := by
      rw [hK, ← Real.sqrt_sq hcpos.le, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖c‖])
    calc ‖c‖⁻¹ = K * (K * ‖c‖)⁻¹ := by field_simp [hKpos.ne', hcpos.ne']
      _ ≤ K * (Real.sqrt (2 * imageCosh (γ i) 1 1))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) hsqle) hKpos.le
      _ ≤ K * Real.exp (-(h3Dist (degPoint 1 one_pos) (h3Act (γ i) (degPoint 1 one_pos))) / 2) :=
          mul_le_mul_of_nonneg_left hexp hKpos.le

/-- **B118′.2 for carriers of discontinuity.** A carrier whose Poincaré series converges at `s = ½`
and which sees `∞` as a point of discontinuity does not carry the torsion kernel. -/
theorem not_carrierSum_eq_torsion_of_poincare {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hP : Summable fun i =>
      Real.exp (-(h3Dist (degPoint 1 one_pos) (h3Act (γ i) (degPoint 1 one_pos))) / 2))
    (horb : ∀ i, (γ i).1 1 0 ≠ 0 → ‖(γ i).1 0 0‖ ≤ R * ‖(γ i).1 1 0‖ ∧
      ‖(γ i).1 1 1‖ ≤ R * ‖(γ i).1 1 0‖ ∧ 1 ≤ R * ‖(γ i).1 1 0‖)
    (hstab : {i | (γ i).1 1 0 = 0}.Finite) (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum γ w m n = κ * (weilPrimeKernel m n : ℂ) :=
  not_carrierSum_eq_torsion (endpointEisenstein_of_poincare hR hP horb hstab) hw hκ

end GaloisForLFunctions.HyperbolicArakelovTheory
