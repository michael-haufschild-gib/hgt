import GaloisForLFunctions.RHTower.ThetaCompactTailSchwartzConvergence
import GaloisForLFunctions.HTGeometry.HurwitzMaxModulusZeros

/-!
# Compact-tail strengthening: exact theta tails with an implanted nonreal zero

For every moment depth `J` and every Schwartz neighbourhood of the literal theta source `k` there
is a strictly positive, even, globally strongly log-concave Schwartz source equal to `k` outside a
compact interval, with the moments of `k` through `J`, whose entire transform has a nonreal zero.

Construction: take `m = J + 1` and `k_t = k + t k^{(4m)}` with `t > 0` small, then the logarithmic
interpolant `b_R` (equal to `k_t` on `[-R, R]` and to `k` outside `[-R-1, R+1]`), then the
correction `g_R = b_R + Σ_ℓ c_ℓ(R) x^{2ℓ} ψ` by a fixed even bump `ψ`. The Gram matrix
`∫ x^{2(i+ℓ)} ψ` is invertible because its quadratic form is `∫ P² ψ`, so the coefficients
`c(R) = -H⁻¹ d(R)` restore the even moments exactly and tend to zero with the moment defects
`d(R)`. As `R → ∞`, `g_R → k_t` in the Schwartz topology and in every exponentially weighted `L¹`
norm; near the bump `g_R = k_t + (small in C²)`, elsewhere `g_R = b_R`, preserving positivity and
strong log-concavity. The transforms converge uniformly near the nonreal packet root
`α_0` of `1 + t z^{4m}`, and the maximum modulus principle applied to `1/G` keeps a zero in a
small disc around `α_0`, away from the real axis.
-/
open Filter Topology Set MeasureTheory Metric
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## The bump and its even moment atoms -/

/-- The even bump `ψ(x) = s(1/16 - x²)`: smooth, positive on `(-1/4, 1/4)`, zero outside. -/
def thetaImplantBump (x : ℝ) : ℝ := Real.smoothTransition (1 / 16 - x ^ 2)

theorem contDiff_thetaImplantBump : ContDiff ℝ ∞ thetaImplantBump :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_id.pow 2))

theorem thetaImplantBump_nonneg (x : ℝ) : 0 ≤ thetaImplantBump x :=
  Real.smoothTransition.nonneg _

theorem thetaImplantBump_pos {x : ℝ} (hx : |x| < 1 / 4) : 0 < thetaImplantBump x := by
  refine Real.smoothTransition.pos_of_pos ?_
  have h1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h2 : |x| ^ 2 < (1 / 4) ^ 2 := by
    have := abs_nonneg x
    nlinarith
  linarith

theorem thetaImplantBump_eq_zero {x : ℝ} (hx : 1 / 4 ≤ |x|) : thetaImplantBump x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith

/-- The moment atom `ψ_ℓ(x) = x^{2ℓ} ψ(x)`. -/
def thetaImplantAtom (l : ℕ) (x : ℝ) : ℝ := x ^ (2 * l) * thetaImplantBump x

theorem contDiff_thetaImplantAtom (l : ℕ) : ContDiff ℝ ∞ (thetaImplantAtom l) :=
  (contDiff_id.pow _).mul contDiff_thetaImplantBump

theorem thetaImplantAtom_neg (l : ℕ) (x : ℝ) : thetaImplantAtom l (-x) = thetaImplantAtom l x := by
  unfold thetaImplantAtom thetaImplantBump
  rw [neg_sq, pow_mul, pow_mul, neg_sq]

theorem thetaImplantAtom_eq_zero (l : ℕ) {x : ℝ} (hx : 1 / 4 ≤ |x|) : thetaImplantAtom l x = 0 := by
  unfold thetaImplantAtom
  rw [thetaImplantBump_eq_zero hx, mul_zero]

theorem hasCompactSupport_thetaImplantAtom (l : ℕ) : HasCompactSupport (thetaImplantAtom l) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (1 / 4)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
  exact thetaImplantAtom_eq_zero l hx.le

theorem integrable_pow_mul_thetaImplantAtom (k l : ℕ) :
    Integrable (fun x : ℝ => x ^ k * thetaImplantAtom l x) :=
  ((continuous_pow k).mul (contDiff_thetaImplantAtom l).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_thetaImplantAtom l).mul_left

/-- The correction `φ_c = Σ_ℓ c_ℓ ψ_ℓ`. -/
def thetaImplantCorrection (N : ℕ) (c : Fin (N + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ l, c l * thetaImplantAtom l x

theorem contDiff_thetaImplantCorrection (N : ℕ) (c : Fin (N + 1) → ℝ) :
    ContDiff ℝ ∞ (thetaImplantCorrection N c) := by
  unfold thetaImplantCorrection
  exact ContDiff.sum fun l _ => contDiff_const.mul (contDiff_thetaImplantAtom l)

theorem thetaImplantCorrection_neg (N : ℕ) (c : Fin (N + 1) → ℝ) (x : ℝ) :
    thetaImplantCorrection N c (-x) = thetaImplantCorrection N c x := by
  simp only [thetaImplantCorrection, thetaImplantAtom_neg]

theorem thetaImplantCorrection_eq_zero (N : ℕ) (c : Fin (N + 1) → ℝ) {x : ℝ} (hx : 1 / 4 ≤ |x|) :
    thetaImplantCorrection N c x = 0 := by
  simp [thetaImplantCorrection, thetaImplantAtom_eq_zero _ hx]

theorem thetaImplantCorrection_eventuallyEq_zero (N : ℕ) (c : Fin (N + 1) → ℝ) {x : ℝ}
    (hx : 1 / 4 < |x|) : thetaImplantCorrection N c =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen {y : ℝ | 1 / 4 < |y|} := isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact thetaImplantCorrection_eq_zero N c (le_of_lt hy)

theorem hasCompactSupport_thetaImplantCorrection (N : ℕ) (c : Fin (N + 1) → ℝ) :
    HasCompactSupport (thetaImplantCorrection N c) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (1 / 4)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
  exact thetaImplantCorrection_eq_zero N c hx.le

/-! ## The even-moment Gram matrix is invertible -/

/-- The Gram matrix `H_{iℓ} = ∫ x^{2i} ψ_ℓ(x) dx`. -/
def thetaImplantGram (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i l => ∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaImplantAtom l x

/-- Pulling a finite even polynomial out of an integral against a compactly supported continuous
function. -/
theorem integral_evenPoly_mul {N : ℕ} (c : Fin (N + 1) → ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    ∫ x : ℝ, (∑ i, c i * x ^ (2 * (i : ℕ))) * g x = ∑ i, c i * ∫ x : ℝ, x ^ (2 * (i : ℕ)) * g x := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · exact (((continuous_const.mul (continuous_pow _)).mul hg).integrable_of_hasCompactSupport
      hgs.mul_left)

theorem integral_pow_mul_thetaImplantCorrection (N : ℕ) (c : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    ∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaImplantCorrection N c x = (thetaImplantGram N).mulVec c i := by
  have hterm : ∀ l : Fin (N + 1), ∫ x : ℝ, x ^ (2 * (i : ℕ)) * (c l * thetaImplantAtom l x) =
      (∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaImplantAtom l x) * c l := by
    intro l
    rw [← integral_mul_const]
    congr 1
    funext x
    ring
  calc ∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaImplantCorrection N c x
      = ∫ x : ℝ, ∑ l, x ^ (2 * (i : ℕ)) * (c l * thetaImplantAtom l x) := by
        congr 1
        funext x
        rw [thetaImplantCorrection, Finset.mul_sum]
    _ = ∑ l, ∫ x : ℝ, x ^ (2 * (i : ℕ)) * (c l * thetaImplantAtom l x) :=
        integral_finsetSum _ fun (l : Fin (N + 1)) _ =>
          ((integrable_pow_mul_thetaImplantAtom (2 * (i : ℕ)) l).const_mul (c l)).congr
            (Eventually.of_forall fun x => by ring)
    _ = ∑ l : Fin (N + 1), (∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaImplantAtom l x) * c l :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = (thetaImplantGram N).mulVec c i := rfl

/-- The quadratic form of the Gram matrix is `∫ (Σ_i c_i x^{2i})² ψ(x) dx`. -/
theorem dotProduct_thetaImplantGram_mulVec (N : ℕ) (c : Fin (N + 1) → ℝ) :
    dotProduct c ((thetaImplantGram N).mulVec c) =
      ∫ x : ℝ, (∑ i, c i * x ^ (2 * (i : ℕ))) ^ 2 * thetaImplantBump x := by
  have hP : Continuous fun x : ℝ => ∑ i, c i * x ^ (2 * (i : ℕ)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow _)
  have hsupp : HasCompactSupport thetaImplantBump := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (1 / 4)) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
    exact thetaImplantBump_eq_zero hx.le
  have h1 : ∀ i, (thetaImplantGram N).mulVec c i =
      ∫ x : ℝ, x ^ (2 * (i : ℕ)) * ((∑ l, c l * x ^ (2 * (l : ℕ))) * thetaImplantBump x) := by
    intro i
    rw [← integral_pow_mul_thetaImplantCorrection]
    congr 1
    funext x
    simp only [thetaImplantCorrection, thetaImplantAtom, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have key := integral_evenPoly_mul c
    (g := fun x => (∑ l, c l * x ^ (2 * (l : ℕ))) * thetaImplantBump x)
    (hP.mul contDiff_thetaImplantBump.continuous) hsupp.mul_left
  simp only [dotProduct, h1]
  rw [← key]
  congr 1
  funext x
  ring

/-- **The Gram matrix is injective**: `H c = 0` forces `∫ P_c² ψ = 0`, so the even polynomial
`P_c` vanishes on `(-1/4, 1/4)` and hence identically. -/
theorem thetaImplantGram_mulVec_eq_zero {N : ℕ} {c : Fin (N + 1) → ℝ}
    (h : (thetaImplantGram N).mulVec c = 0) : c = 0 := by
  have hq := dotProduct_thetaImplantGram_mulVec N c
  rw [h, dotProduct_zero] at hq
  set P : ℝ → ℝ := fun x => ∑ i, c i * x ^ (2 * (i : ℕ))
  have hP : Continuous P := continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow _)
  have hcont : Continuous fun x => P x ^ 2 * thetaImplantBump x :=
    (hP.pow 2).mul contDiff_thetaImplantBump.continuous
  have hsupp : HasCompactSupport fun x => P x ^ 2 * thetaImplantBump x := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (1 / 4)) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
    simp [thetaImplantBump_eq_zero hx.le]
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => mul_nonneg (sq_nonneg (P x)) (thetaImplantBump_nonneg x))
    (hcont.integrable_of_hasCompactSupport hsupp)).1 hq.symm
  have hzero := (Continuous.ae_eq_iff_eq volume hcont continuous_const).1 hae
  have hroot : ∀ x ∈ Ioo (-(1 / 4) : ℝ) (1 / 4), P x = 0 := by
    intro x hx
    have hb := thetaImplantBump_pos (abs_lt.2 ⟨hx.1, hx.2⟩)
    have h0 := congrFun hzero x
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      ((mul_eq_zero.1 h0).resolve_right hb.ne')
  set Q : Polynomial ℝ := ∑ i, Polynomial.C (c i) * Polynomial.X ^ (2 * (i : ℕ))
  have hQeval : ∀ x, Q.eval x = P x := by
    intro x
    simp [Q, P, Polynomial.eval_finsetSum]
  have hQ : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
    refine Set.Infinite.mono (fun x hx => ?_) (Set.Ioo_infinite (by norm_num : (-(1 / 4) : ℝ) < 1 / 4))
    simp only [mem_setOf_eq, Polynomial.IsRoot.def, hQeval]
    exact hroot x hx
  funext i
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (2 * (i : ℕ))) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun l _ hl => by
    rw [if_neg]
    intro h2
    exact hl (Fin.ext (by omega))) (by simp)] at hc
  simpa using hc

theorem thetaImplantGram_mulVec_injective (N : ℕ) :
    Function.Injective (thetaImplantGram N).mulVec := by
  intro a b hab
  have h : (thetaImplantGram N).mulVec (a - b) = 0 := by
    rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.1 (thetaImplantGram_mulVec_eq_zero h)

/-! ## The correction in Schwartz space -/

/-- The atom `ψ_ℓ` as a Schwartz function. -/
def thetaImplantAtomSchwartz (l : ℕ) : SchwartzMap ℝ ℝ :=
  (hasCompactSupport_thetaImplantAtom l).toSchwartzMap (contDiff_thetaImplantAtom l)

/-- The correction `φ_c` as a Schwartz function. -/
def thetaImplantCorrectionSchwartz (N : ℕ) (c : Fin (N + 1) → ℝ) : SchwartzMap ℝ ℝ :=
  ∑ l, c l • thetaImplantAtomSchwartz l

theorem thetaImplantCorrectionSchwartz_apply (N : ℕ) (c : Fin (N + 1) → ℝ) (x : ℝ) :
    thetaImplantCorrectionSchwartz N c x = thetaImplantCorrection N c x := by
  simp [thetaImplantCorrectionSchwartz, thetaImplantAtomSchwartz,
    thetaImplantCorrection]

theorem continuous_thetaImplantCorrectionSchwartz (N : ℕ) :
    Continuous (thetaImplantCorrectionSchwartz N) :=
  continuous_finsetSum _ fun l _ => (continuous_apply l).smul continuous_const

theorem thetaImplantCorrectionSchwartz_zero (N : ℕ) : thetaImplantCorrectionSchwartz N 0 = 0 := by
  simp [thetaImplantCorrectionSchwartz]

/-- Small coefficients give a correction that is uniformly small together with its first two
derivatives. -/
theorem eventually_abs_iteratedDeriv_thetaImplantCorrection_le (N : ℕ) {u : ℝ} (hu : 0 < u) :
    ∀ᶠ c in 𝓝 (0 : Fin (N + 1) → ℝ), ∀ j ≤ 2, ∀ x : ℝ,
      |iteratedDeriv j (thetaImplantCorrection N c) x| ≤ u := by
  have hT : Tendsto (thetaImplantCorrectionSchwartz N) (𝓝 0) (𝓝 0) := by
    have := (continuous_thetaImplantCorrectionSchwartz N).tendsto 0
    rwa [thetaImplantCorrectionSchwartz_zero] at this
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds] at hT
  have h := fun j : Fin 3 => hT (0, (j : ℕ)) u hu
  filter_upwards [eventually_all.2 h] with c hc j hj x
  have hcoe : (⇑(thetaImplantCorrectionSchwartz N c) : ℝ → ℝ) = thetaImplantCorrection N c :=
    funext (thetaImplantCorrectionSchwartz_apply N c)
  have := SchwartzMap.le_seminorm ℝ 0 j (thetaImplantCorrectionSchwartz N c) x
  rw [pow_zero, one_mul, hcoe, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at this
  have hlt := hc ⟨j, by omega⟩
  simp only [sub_zero] at hlt
  exact this.trans hlt.le

/-- The exponentially weighted `L¹` size of the correction tends to zero with the coefficients. -/
theorem tendsto_integral_exp_mul_abs_thetaImplantCorrection (N : ℕ) (c₀ : ℝ) :
    Tendsto (fun c : Fin (N + 1) → ℝ => ∫ x, Real.exp (c₀ * |x|) * |thetaImplantCorrection N c x|)
      (𝓝 0) (𝓝 0) := by
  set I : Fin (N + 1) → ℝ := fun l => ∫ x, Real.exp (c₀ * |x|) * |thetaImplantAtom l x|
  have hint : ∀ l : Fin (N + 1), Integrable fun x => Real.exp (c₀ * |x|) * |thetaImplantAtom l x| :=
    fun l => (((continuous_const.mul continuous_abs).rexp).mul
      (contDiff_thetaImplantAtom l).continuous.abs).integrable_of_hasCompactSupport
      (hasCompactSupport_thetaImplantAtom l).abs.mul_left
  have hbound : ∀ c : Fin (N + 1) → ℝ,
      ∫ x, Real.exp (c₀ * |x|) * |thetaImplantCorrection N c x| ≤ ∑ l, |c l| * I l := by
    intro c
    have hle : ∀ x, Real.exp (c₀ * |x|) * |thetaImplantCorrection N c x| ≤
        ∑ l, |c l| * (Real.exp (c₀ * |x|) * |thetaImplantAtom l x|) := by
      intro x
      have h := Finset.abs_sum_le_sum_abs (fun l => c l * thetaImplantAtom l x) Finset.univ
      have he := Real.exp_pos (c₀ * |x|)
      calc Real.exp (c₀ * |x|) * |thetaImplantCorrection N c x|
          ≤ Real.exp (c₀ * |x|) * ∑ l, |c l * thetaImplantAtom l x| :=
            mul_le_mul_of_nonneg_left h he.le
        _ = ∑ l, |c l| * (Real.exp (c₀ * |x|) * |thetaImplantAtom l x|) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [abs_mul]; ring
    calc ∫ x, Real.exp (c₀ * |x|) * |thetaImplantCorrection N c x|
        ≤ ∫ x, ∑ l, |c l| * (Real.exp (c₀ * |x|) * |thetaImplantAtom l x|) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
            (integrable_finsetSum _ fun l _ => (hint l).const_mul _)
            (Eventually.of_forall hle)
      _ = ∑ l, |c l| * I l := by
          rw [integral_finsetSum _ fun l _ => (hint l).const_mul _]
          exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hlim : Tendsto (fun c : Fin (N + 1) → ℝ => ∑ l, |c l| * I l) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun c : Fin (N + 1) → ℝ => ∑ l, |c l| * I l :=
      continuous_finsetSum _ fun l _ => ((continuous_apply l).abs).mul continuous_const
    simpa using hc.tendsto 0
  refine squeeze_zero (fun c => by positivity) hbound hlim

/-! ## Curvature near the bump -/

/-- Additive form of the perturbed numerator bound: perturbations `e_j` of size `≤ u` with `u`
small keep `k₀ + e₀ > 0` and a uniformly negative normalized numerator. -/
theorem thetaPacket_additive_numerator_le {k0 k1 k2 e0 e1 e2 u B η κ : ℝ}
    (hk0 : |k0| ≤ B) (hk1 : |k1| ≤ B) (hk2 : |k2| ≤ B) (he0 : |e0| ≤ u) (he1 : |e1| ≤ u)
    (he2 : |e2| ≤ u) (hB : 1 ≤ B) (hN0 : k2 * k0 - k1 ^ 2 ≤ -η) (hκk : κ ≤ k0) (hκ : 0 < κ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (huη : u * (12 * B ^ 2 + 1) ≤ η) (huκ : u * (2 * B) ≤ κ) :
    0 < k0 + e0 ∧ (k2 + e2) * (k0 + e0) - (k1 + e1) ^ 2 ≤
      -(η / (2 * (4 * B ^ 2 + 1))) * (k0 + e0) ^ 2 := by
  rcases hu0.eq_or_lt with hu | hu
  · subst hu
    have h0 : e0 = 0 := abs_nonpos_iff.1 he0
    have h1 : e1 = 0 := abs_nonpos_iff.1 he1
    have h2 : e2 = 0 := abs_nonpos_iff.1 he2
    subst h0 h1 h2
    have := thetaPacket_compact_numerator_le (d0 := 0) (d1 := 0) (d2 := 0) hk0 hk1 hk2
      (by simp; linarith) (by simp; linarith) (by simp; linarith) hB hN0 hκk hκ le_rfl zero_le_one
      (by simpa using huη) (by simpa using huκ)
    simpa using this
  · have hd : ∀ {e : ℝ}, |e| ≤ u → |e / u| ≤ B := fun {e} he => by
      rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]
      nlinarith
    have h := thetaPacket_compact_numerator_le (d0 := e0 / u) (d1 := e1 / u) (d2 := e2 / u) hk0 hk1
      hk2 (hd he0) (hd he1) (hd he2) hB hN0 hκk hκ hu.le hu1 huη huκ
    simp only [mul_div_cancel₀ _ hu.ne'] at h
    exact h

/-- The second logarithmic derivative of a positive smooth function. -/
theorem iteratedDeriv_two_log_of_pos {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x)
    (x : ℝ) :
    iteratedDeriv 2 (fun y => Real.log (g y)) x =
      (iteratedDeriv 2 g x * g x - iteratedDeriv 1 g x ^ 2) / g x ^ 2 := by
  rw [iteratedDeriv_succ_log hg hpos 1, iteratedDeriv_one, deriv_iteratedDeriv_div hg hpos 1]
  have := (hpos x).ne'
  field_simp

/-- Near the bump, additive perturbations of `k_t` of size `≤ u₀` keep positivity and uniform
strong log-concavity. -/
theorem exists_thetaDerivativePacket_bump_region {m : ℕ} {t : ℝ}
    (hpos : ∀ x, 0 < thetaDerivativePacket m t x) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hN : ∀ x, thetaDerivativePacketNumerator m t x ≤ -δ₁ * thetaDerivativePacket m t x ^ 2) :
    ∃ u₀ > 0, ∃ δ₂ > 0, ∀ x : ℝ, |x| ≤ 1 / 2 → ∀ e0 e1 e2 : ℝ, |e0| ≤ u₀ → |e1| ≤ u₀ →
      |e2| ≤ u₀ → 0 < thetaDerivativePacket m t x + e0 ∧
        (iteratedDeriv 2 (thetaDerivativePacket m t) x + e2) * (thetaDerivativePacket m t x + e0) -
          (iteratedDeriv 1 (thetaDerivativePacket m t) x + e1) ^ 2 ≤
            -δ₂ * (thetaDerivativePacket m t x + e0) ^ 2 := by
  have hK : IsCompact (Icc (-(1 / 2) : ℝ) (1 / 2)) := isCompact_Icc
  have hKne : (Icc (-(1 / 2) : ℝ) (1 / 2)).Nonempty := ⟨0, by constructor <;> norm_num⟩
  have hc := contDiff_thetaDerivativePacket m t
  have hc1 : Continuous (iteratedDeriv 1 (thetaDerivativePacket m t)) :=
    hc.continuous_iteratedDeriv 1 (by norm_cast)
  have hc2 : Continuous (iteratedDeriv 2 (thetaDerivativePacket m t)) :=
    hc.continuous_iteratedDeriv 2 (by norm_cast)
  obtain ⟨x₁, -, hx₁⟩ := hK.exists_isMinOn hKne hc.continuous.continuousOn
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = thetaDerivativePacket m t x₁ := ⟨_, rfl⟩
  have hκ : 0 < κ := hκdef ▸ hpos x₁
  have hg : Continuous fun x => |thetaDerivativePacket m t x| +
      |iteratedDeriv 1 (thetaDerivativePacket m t) x| +
      |iteratedDeriv 2 (thetaDerivativePacket m t) x| := by
    have := hc.continuous; fun_prop
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max B₀ 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := hBdef ▸ le_max_right _ _
  have hBd : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), |thetaDerivativePacket m t x| +
      |iteratedDeriv 1 (thetaDerivativePacket m t) x| +
      |iteratedDeriv 2 (thetaDerivativePacket m t) x| ≤ B := fun x hx =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB₀ x hx)).trans
      (hBdef ▸ le_max_left _ _)
  set η := δ₁ * κ ^ 2
  have hη : 0 < η := by positivity
  have hB0 : 0 < B := by linarith
  refine ⟨min 1 (min (η / (12 * B ^ 2 + 1)) (κ / (2 * B))), by positivity,
    η / (2 * (4 * B ^ 2 + 1)), by positivity, fun x hx e0 e1 e2 h0 h1 h2 => ?_⟩
  have hxK : x ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := ⟨(abs_le.1 hx).1, (abs_le.1 hx).2⟩
  have hb := hBd x hxK
  have a0 := abs_nonneg (thetaDerivativePacket m t x)
  have a1 := abs_nonneg (iteratedDeriv 1 (thetaDerivativePacket m t) x)
  have a2 := abs_nonneg (iteratedDeriv 2 (thetaDerivativePacket m t) x)
  have hκx : κ ≤ thetaDerivativePacket m t x := hκdef ▸ hx₁ hxK
  have hN0 : iteratedDeriv 2 (thetaDerivativePacket m t) x * thetaDerivativePacket m t x -
      iteratedDeriv 1 (thetaDerivativePacket m t) x ^ 2 ≤ -η := by
    have h := hN x
    unfold thetaDerivativePacketNumerator at h
    have hsq : κ ^ 2 ≤ thetaDerivativePacket m t x ^ 2 := pow_le_pow_left₀ hκ.le hκx 2
    have := mul_le_mul_of_nonneg_left hsq hδ₁.le
    simp only [η]
    linarith
  set u := min 1 (min (η / (12 * B ^ 2 + 1)) (κ / (2 * B)))
  have hu0 : 0 ≤ u := by positivity
  exact thetaPacket_additive_numerator_le (by linarith) (by linarith) (by linarith) h0 h1 h2 hB1
    hN0 hκx hκ hu0 (min_le_left _ _)
    ((le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_left _ _)))
    ((le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_right _ _)))

/-! ## Transforms -/

theorem expMomentSource_ofReal_of_hasCompactSupport_sub {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport fun x => g x - thetaCuspFullSource x) :
    ExpMomentSource (fun x => (g x : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp hg, fun c => ?_⟩
  have h1 : Integrable fun x => Real.exp (c * |x|) * |g x - thetaCuspFullSource x| :=
    (((continuous_const.mul continuous_abs).rexp).mul
      (hg.sub contDiff_thetaCuspFullSource.continuous).abs).integrable_of_hasCompactSupport
      hs.abs.mul_left
  have h2 := integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 0 c
  refine (h1.add h2).mono' (by
    have := Complex.continuous_ofReal.comp hg
    exact (by fun_prop : Continuous fun x => Real.exp (c * |x|) * ‖(g x : ℂ)‖).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs]
  simp only [Pi.add_apply, iteratedDeriv_zero]
  have := abs_sub_abs_le_abs_sub (g x) (thetaCuspFullSource x)
  have he := Real.exp_pos (c * |x|)
  nlinarith

/-- Two sources with every exponential moment have transforms differing by at most the
exponentially weighted `L¹` distance, uniformly on horizontal strips. -/
theorem norm_sourceTransform_sub_le {f h : ℝ → ℂ} (hf : ExpMomentSource f)
    (hh : ExpMomentSource h) (z : ℂ) {c : ℝ} (hc : |z.im| ≤ c) :
    ‖sourceTransform f z - sourceTransform h z‖ ≤ ∫ x, Real.exp (c * |x|) * ‖f x - h x‖ := by
  unfold sourceTransform
  rw [← integral_sub (hf.integrable_cexp z) (hh.integrable_cexp z)]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) ?_ (Eventually.of_forall fun x => ?_))
  · refine ((hf.moment c).add (hh.moment c)).mono' (by
      have := hf.continuous; have := hh.continuous
      exact (by fun_prop : Continuous fun x => Real.exp (c * |x|) * ‖f x - h x‖).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
  · simp only
    rw [← mul_sub, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    apply Real.exp_le_exp.2
    have hre : (-Complex.I * z * x).re = z.im * x := by simp [Complex.mul_re]
    rw [hre]
    calc z.im * x ≤ |z.im * x| := le_abs_self _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ c * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)

/-! ## Moments of even sources -/

theorem integral_pow_mul_eq_zero_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) {j : ℕ} (hj : Odd j) :
    ∫ x : ℝ, x ^ j * f x = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => x ^ j * f x) volume
  simp only [hf, hj.neg_pow, neg_mul, integral_neg] at h
  linarith

theorem integrable_pow_mul_of_hasCompactSupport_sub {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport fun x => f x - thetaCuspFullSource x) (j : ℕ) :
    Integrable fun x : ℝ => x ^ j * f x := by
  have h1 : Integrable fun x : ℝ => x ^ j * (f x - thetaCuspFullSource x) :=
    ((continuous_pow j).mul (hf.sub contDiff_thetaCuspFullSource.continuous)
      ).integrable_of_hasCompactSupport hs.mul_left
  have h2 : Integrable fun x : ℝ => x ^ j * thetaCuspFullSource x := by
    simpa using integrable_pow_mul_iteratedDeriv_thetaCuspFullSource 0 j
  exact (h1.add h2).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)

/-! ## The compact-tail strengthening -/

/-- **Compact-tail strengthening.** For every moment depth `J` and every Schwartz neighbourhood
`U` of the literal theta source there is a strictly positive, even, globally strongly log-concave
Schwartz source `g ∈ U` that equals `k` outside a compact interval, has the moments of `k` through
order `J`, and whose entire transform has a nonreal zero. -/
theorem exists_thetaCompactTailImplant (J : ℕ) {U : Set (SchwartzMap ℝ ℝ)}
    (hU : U ∈ 𝓝 thetaCuspSchwartzReal) :
    ∃ g : SchwartzMap ℝ ℝ, g ∈ U ∧ (∀ x, 0 < g x) ∧ (∀ x, g (-x) = g x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (g y)) x ≤ -δ) ∧
      (∃ R : ℝ, ∀ x, R ≤ |x| → g x = thetaCuspFullSource x) ∧
      (∀ j ≤ J, ∫ x : ℝ, x ^ j * g x = ∫ x : ℝ, x ^ j * thetaCuspFullSource x) ∧
      ∃ z : ℂ, z.im ≠ 0 ∧ sourceTransform (fun x => (g x : ℂ)) z = 0 := by
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = J + 1 := ⟨_, rfl⟩
  have hm : 0 < m := by omega
  obtain ⟨ε, hε, δ, hδ, hSLC⟩ := exists_thetaDerivativePacket_stronglyLogConcave m hm
  obtain ⟨ε', hε', δ₁, hδ₁, hNum⟩ := exists_thetaDerivativePacket_numerator_le m hm
  obtain ⟨V, hVU, hVo, hkV⟩ := mem_nhds_iff.1 hU
  -- the deformation parameter
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      thetaDerivativePacketSchwartz m t ∈ V ∧ 0 < t ∧ t < min ε ε' := by
    filter_upwards [((tendsto_thetaDerivativePacketSchwartz m).mono_left nhdsWithin_le_nhds)
      (hVo.mem_nhds hkV), self_mem_nhdsWithin, Ioo_mem_nhdsGT (lt_min hε hε')] with t h1 h2 h3
    exact ⟨h1, h2, h3.2⟩
  obtain ⟨t, htV, ht, htε⟩ := hev.exists
  have htε1 : t < ε := htε.trans_le (min_le_left _ _)
  have htε2 : t < ε' := htε.trans_le (min_le_right _ _)
  have hpos : ∀ x, 0 < thetaDerivativePacket m t x := (hSLC t ht.le htε1).1
  have hNt : ∀ x, thetaDerivativePacketNumerator m t x ≤ -δ₁ * thetaDerivativePacket m t x ^ 2 :=
    fun x => (hNum t ht.le htε2 x).2
  obtain ⟨R₀, -, hbSLC⟩ :=
    exists_thetaTailInterpolant_stronglyLogConcave hpos hm ht.le (hSLC t ht.le htε1).2
  obtain ⟨u₀, hu₀, δ₂, hδ₂, hbump⟩ := exists_thetaDerivativePacket_bump_region hpos hδ₁ hNt
  -- a circle around the first packet root on which `F_t` stays away from zero
  have hαim : 0 < (thetaPacketRoot m t 0).im := by
    rw [thetaPacketRoot_im]
    refine mul_pos (Real.rpow_pos_of_pos ht _) (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [Real.pi_pos]
  have hFd := differentiable_sourceTransform_thetaDerivativePacketC m t
  have hF0 : sourceTransform (thetaDerivativePacketC m t) 0 ≠ 0 := by
    rw [sourceTransform_thetaDerivativePacketC]
    simpa [zero_pow (by omega : 4 * m ≠ 0)] using XiC_ne_zero_of_norm_le_one (by simp)
  obtain ⟨ρ, hρ, hρα, m₀, hm₀, hsphere⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sphere_norm_ge_of_differentiable hFd hF0
      (thetaPacketRoot m t 0) hαim
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (thetaPacketRoot m t 0).im + ρ := ⟨_, rfl⟩
  -- the moment correction
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = J / 2 := ⟨_, rfl⟩
  have hinj : Function.Injective (Matrix.mulVecLin (thetaImplantGram N)) := by
    intro a b hab
    exact thetaImplantGram_mulVec_injective N (by simpa [Matrix.mulVecLin_apply] using hab)
  obtain ⟨e, he⟩ : ∃ e : (Fin (N + 1) → ℝ) ≃ₗ[ℝ] (Fin (N + 1) → ℝ),
      e = LinearEquiv.ofInjectiveEndo _ hinj := ⟨_, rfl⟩
  have heH : ∀ v, (thetaImplantGram N).mulVec v = e v := fun v => by
    rw [he]; rfl
  set d : ℝ → Fin (N + 1) → ℝ := fun R i =>
    (∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaTailInterpolant m t R x) -
      ∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaCuspFullSource x
  set c : ℝ → Fin (N + 1) → ℝ := fun R => e.symm (-d R)
  have hHc : ∀ R, (thetaImplantGram N).mulVec (c R) = -d R := fun R => by
    rw [heH]; exact e.apply_symm_apply _
  have hd : Tendsto d atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have hi : 2 * (i : ℕ) < 4 * m := by have := i.isLt; omega
    have h1 := (tendsto_integral_pow_mul_thetaTailInterpolant hpos hm ht.le (2 * (i : ℕ))).sub_const
      (∫ x : ℝ, x ^ (2 * (i : ℕ)) * thetaCuspFullSource x)
    rw [integral_pow_mul_thetaDerivativePacket_of_lt m t hi, sub_self] at h1
    exact h1
  have hcR : Tendsto c atTop (𝓝 0) := by
    have hcont : Continuous fun v : Fin (N + 1) → ℝ => e.symm v :=
      LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
    have hdn : Tendsto (fun R => -d R) atTop (𝓝 0) := by simpa using hd.neg
    have := (hcont.tendsto 0).comp hdn
    rw [map_zero] at this
    exact this
  -- the candidate sources
  set g : ℝ → SchwartzMap ℝ ℝ := fun R =>
    thetaTailInterpolantSchwartz hpos R + thetaImplantCorrectionSchwartz N (c R)
  have hgx : ∀ R x, g R x = thetaTailInterpolant m t R x + thetaImplantCorrection N (c R) x := by
    intro R x
    simp only [g, add_apply, thetaTailInterpolantSchwartz_apply, thetaImplantCorrectionSchwartz_apply]
  have hgT : Tendsto g atTop (𝓝 (thetaDerivativePacketSchwartz m t)) := by
    have h1 := tendsto_thetaTailInterpolantSchwartz hpos hm ht.le
    have h2 : Tendsto (fun R => thetaImplantCorrectionSchwartz N (c R)) atTop (𝓝 0) := by
      have := ((continuous_thetaImplantCorrectionSchwartz N).tendsto 0).comp hcR
      rwa [thetaImplantCorrectionSchwartz_zero] at this
    simpa using h1.add h2
  have hsum : Tendsto (fun R => (∫ x, Real.exp (c₀ * |x|) *
      |thetaTailInterpolant m t R x - thetaDerivativePacket m t x|) +
        ∫ x, Real.exp (c₀ * |x|) * |thetaImplantCorrection N (c R) x|) atTop (𝓝 0) := by
    have h1 := tendsto_integral_exp_mul_abs_thetaTailInterpolant_sub hpos hm ht.le c₀
    have h2 := (tendsto_integral_exp_mul_abs_thetaImplantCorrection N c₀).comp hcR
    simpa using h1.add h2
  obtain ⟨R, hRR, hgV, hsmall, hclose⟩ := ((eventually_ge_atTop (max R₀ 1)).and
    ((hgT.eventually_mem (hVo.mem_nhds htV)).and
      ((hcR.eventually (eventually_abs_iteratedDeriv_thetaImplantCorrection_le N hu₀)).and
        (hsum.eventually (gt_mem_nhds (half_pos hm₀)))))).exists
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hRR
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans hRR
  set φ := thetaImplantCorrection N (c R)
  set b := thetaTailInterpolant m t R
  have hgx' : ∀ x, g R x = b x + φ x := fun x => hgx R x
  have hbS : HasCompactSupport fun x => b x - thetaCuspFullSource x :=
    hasCompactSupport_thetaTailInterpolant_sub_source R
  have hφc : ContDiff ℝ ∞ φ := contDiff_thetaImplantCorrection N (c R)
  have hbc : ContDiff ℝ ∞ b := contDiff_thetaTailInterpolant hpos R
  have hgfun : (⇑(g R) : ℝ → ℝ) = fun x => b x + φ x := funext hgx'
  have hgc : ContDiff ℝ ∞ (g R) := hgfun ▸ hbc.add hφc
  -- near the bump, `g = k_t + φ`
  have hnear : ∀ x, |x| ≤ 1 / 2 → (⇑(g R) : ℝ → ℝ) =ᶠ[𝓝 x]
      fun y => thetaDerivativePacket m t y + φ y := by
    intro x hx
    have hxR : |x| < R := by linarith
    filter_upwards [thetaTailInterpolant_eventuallyEq_packet hpos hxR] with y hy
    rw [hgfun]
    simp only [b] at hy ⊢
    rw [hy]
  have hderiv : ∀ x, |x| ≤ 1 / 2 → ∀ j, iteratedDeriv j (g R) x =
      iteratedDeriv j (thetaDerivativePacket m t) x + iteratedDeriv j φ x := by
    intro x hx j
    rw [(hnear x hx).iteratedDeriv_eq]
    exact iteratedDeriv_add ((contDiff_thetaDerivativePacket m t).contDiffAt.of_le
      (by norm_cast; exact le_top)) (hφc.contDiffAt.of_le (by norm_cast; exact le_top))
  have hsm : ∀ x, |φ x| ≤ u₀ ∧ |iteratedDeriv 1 φ x| ≤ u₀ ∧ |iteratedDeriv 2 φ x| ≤ u₀ :=
    fun x => ⟨by simpa using hsmall 0 (by norm_num) x, hsmall 1 (by norm_num) x,
      hsmall 2 le_rfl x⟩
  -- positivity
  have hgpos : ∀ x, 0 < g R x := by
    intro x
    rw [hgx']
    rcases le_or_gt |x| (1 / 2) with hx | hx
    · have h := (hbump x hx (φ x) (iteratedDeriv 1 φ x) (iteratedDeriv 2 φ x) (hsm x).1 (hsm x).2.1
        (hsm x).2.2).1
      have hbx : b x = thetaDerivativePacket m t x :=
        (thetaTailInterpolant_eventuallyEq_packet hpos (by linarith : |x| < R)).self_of_nhds
      rw [hbx]
      exact h
    · have hφx : φ x = 0 := thetaImplantCorrection_eq_zero N (c R) (by linarith)
      rw [hφx, add_zero]
      exact thetaTailInterpolant_pos R x
  refine ⟨g R, hVU hgV, hgpos, fun x => ?_, ⟨min (min 1 δ) δ₂, by positivity, fun x => ?_⟩,
    ⟨R + 1, fun x hx => ?_⟩, fun j hj => ?_, ?_⟩
  · -- evenness
    rw [hgx', hgx']
    exact congrArg₂ (· + ·) (thetaTailInterpolant_neg R x) (thetaImplantCorrection_neg N (c R) x)
  · -- strong log-concavity
    rcases le_or_gt |x| (1 / 4) with hx | hx
    · have hx2 : |x| ≤ 1 / 2 := by linarith
      rw [iteratedDeriv_two_log_of_pos hgc hgpos, hderiv x hx2, hderiv x hx2]
      have hgxv : g R x = thetaDerivativePacket m t x + φ x := (hnear x hx2).self_of_nhds
      rw [hgxv]
      obtain ⟨hp, hn⟩ := hbump x hx2 (φ x) (iteratedDeriv 1 φ x) (iteratedDeriv 2 φ x) (hsm x).1
        (hsm x).2.1 (hsm x).2.2
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ -δ₂ * (thetaDerivativePacket m t x + φ x) ^ 2 := hn
        _ ≤ -min (min 1 δ) δ₂ * (thetaDerivativePacket m t x + φ x) ^ 2 :=
          mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
    · have heq : (fun y => Real.log (g R y)) =ᶠ[𝓝 x] fun y => Real.log (b y) := by
        filter_upwards [thetaImplantCorrection_eventuallyEq_zero N (c R) hx] with y hy
        rw [hgx']
        have hy' : φ y = 0 := hy
        rw [hy', add_zero]
      rw [heq.iteratedDeriv_eq]
      exact (hbSLC R hRR₀ x).trans (neg_le_neg ((min_le_left _ _)))
  · -- equality with `k` outside a compact interval
    rw [hgx']
    change thetaTailInterpolant m t R x + thetaImplantCorrection N (c R) x = _
    rw [thetaTailInterpolant_eq_source hx, thetaImplantCorrection_eq_zero N (c R)
      (by linarith), add_zero]
  · -- the moments through `J`
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hodd
    · have hiN : i < N + 1 := by omega
      set i' : Fin (N + 1) := ⟨i, hiN⟩
      have hji : i + i = 2 * (i' : ℕ) := by simp [i']; ring
      rw [hji]
      have hI1 := integrable_pow_mul_of_hasCompactSupport_sub hbc.continuous hbS (2 * (i' : ℕ))
      have hI2 : Integrable fun x : ℝ => x ^ (2 * (i' : ℕ)) * φ x :=
        ((continuous_pow _).mul hφc.continuous).integrable_of_hasCompactSupport
          (hasCompactSupport_thetaImplantCorrection N (c R)).mul_left
      have hsplit : ∫ x : ℝ, x ^ (2 * (i' : ℕ)) * g R x =
          (∫ x : ℝ, x ^ (2 * (i' : ℕ)) * b x) + ∫ x : ℝ, x ^ (2 * (i' : ℕ)) * φ x := by
        rw [← integral_add hI1 hI2]
        congr 1
        funext x
        rw [hgx']
        ring
      rw [hsplit, integral_pow_mul_thetaImplantCorrection, hHc R]
      simp only [Pi.neg_apply, d]
      ring
    · have hgeven : ∀ x, g R (-x) = g R x := fun x => by
        rw [hgx', hgx']
        exact congrArg₂ (· + ·) (thetaTailInterpolant_neg R x) (thetaImplantCorrection_neg N (c R) x)
      rw [integral_pow_mul_eq_zero_of_odd hgeven hodd,
        integral_pow_mul_eq_zero_of_odd thetaCuspFullSource_neg hodd]
  · -- a nonreal zero of the transform
    have hgS : HasCompactSupport fun x => g R x - thetaCuspFullSource x := by
      have h := hbS.add (hasCompactSupport_thetaImplantCorrection N (c R))
      have heq : (fun x => g R x - thetaCuspFullSource x) =
          (fun x => b x - thetaCuspFullSource x) + φ := by
        funext x
        simp only [Pi.add_apply]
        rw [hgx']
        ring
      rw [heq]
      exact h
    have hG := expMomentSource_ofReal_of_hasCompactSupport_sub hgc.continuous hgS
    have hGd := hG.differentiable_sourceTransform
    have hFα := sourceTransform_thetaDerivativePacketC_root m hm ht 0
    have hcl : ∀ z ∈ closedBall (thetaPacketRoot m t 0) ρ,
        ‖sourceTransform (fun x => (g R x : ℂ)) z -
          sourceTransform (thetaDerivativePacketC m t) z‖ < m₀ / 2 := by
      intro z hz
      have hzim : |z.im| ≤ c₀ := by
        have h1 : |z.im - (thetaPacketRoot m t 0).im| ≤ ρ := by
          rw [mem_closedBall, dist_eq_norm] at hz
          exact (Complex.abs_im_le_norm _).trans (by simpa using hz)
        rw [hc₀, abs_le]
        constructor <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2]
      refine lt_of_le_of_lt (norm_sourceTransform_sub_le hG
        (expMomentSource_thetaDerivativePacketC m t) z hzim) (lt_of_le_of_lt ?_ hclose)
      have hA : Integrable fun x => Real.exp (c₀ * |x|) *
          |b x - thetaDerivativePacket m t x| := by
        have h1 : Integrable fun x => Real.exp (c₀ * |x|) * |b x - thetaCuspFullSource x| :=
          (((continuous_const.mul continuous_abs).rexp).mul
            (hbc.continuous.sub contDiff_thetaCuspFullSource.continuous).abs
            ).integrable_of_hasCompactSupport hbS.abs.mul_left
        have h2 := (integrable_exp_abs_mul_abs_thetaDerivativePacket m t c₀).add
          (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 0 c₀)
        refine (h1.add h2).mono' (by
          have := hbc.continuous; have := (contDiff_thetaDerivativePacket m t).continuous
          exact (by fun_prop : Continuous fun x => Real.exp (c₀ * |x|) *
            |b x - thetaDerivativePacket m t x|).aestronglyMeasurable)
          (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        simp only [Pi.add_apply, iteratedDeriv_zero]
        have he := Real.exp_pos (c₀ * |x|)
        have := abs_sub_le (b x) (thetaCuspFullSource x) (thetaDerivativePacket m t x)
        have h3 : |thetaCuspFullSource x - thetaDerivativePacket m t x| ≤
            |thetaDerivativePacket m t x| + |thetaCuspFullSource x| := by
          rw [abs_sub_comm]; exact abs_sub _ _
        nlinarith
      have hB : Integrable fun x => Real.exp (c₀ * |x|) * |φ x| :=
        (((continuous_const.mul continuous_abs).rexp).mul hφc.continuous.abs
          ).integrable_of_hasCompactSupport (hasCompactSupport_thetaImplantCorrection N (c R)).abs.mul_left
      rw [← integral_add hA hB]
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) (hA.add hB)
        (Eventually.of_forall fun x => ?_)
      simp only [thetaDerivativePacketC]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hgx', ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have := abs_add_le (b x - thetaDerivativePacket m t x) (φ x)
      calc |b x + φ x - thetaDerivativePacket m t x| = |b x - thetaDerivativePacket m t x + φ x| := by
            ring_nf
        _ ≤ _ := this
    obtain ⟨z, hz, hz0⟩ := GaloisForLFunctions.HTGeometry.exists_zero_mem_closedBall_of_norm_sub_lt
      hρ hGd hFα hsphere hcl
    refine ⟨z, ?_, hz0⟩
    have h1 : |z.im - (thetaPacketRoot m t 0).im| ≤ ρ := by
      rw [mem_closedBall, dist_eq_norm] at hz
      exact (Complex.abs_im_le_norm _).trans (by simpa using hz)
    have : 0 < z.im := by linarith [(abs_le.1 h1).1]
    exact this.ne'

end

end RHTower
