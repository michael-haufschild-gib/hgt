import GaloisForLFunctions.RHTower.Heat.HeatZeroDisplacement

/-!
# The depth law sees only the crowd

How long does a zero of the flow persist? Run the Gaussian representation backward from time `t₁ = t₀ + t` to time `t₀` around a saddle: if `H_{t₁}`
has no zero within distance `d` of a zero `z` of `H_{t₀}`, then the local shape of `H_{t₁}` on real segments is controlled by the field
`V = H'/H` near `z` and by the **zero energy**

`R₂(z) = Σ_a m_a/|z − a|²`,

the sum over the packet of `H_{t₁}`, and the representation forces `H_{t₀}(z) ≠ 0` as soon as

`t|V| ≤ c d`,  `t R₂(z) ≤ c`,  `t log X ≤ c d`    (`exists_zero_near_of_no_crowd`).

So the depth law is **linear unless there is a crowd**. A packet at normal density has `R₂ ≍ log X/d` and `|V| ≪ log X`, and then a zero persists until
`t ≍ d/log X`. The quadratic law `t ≍ d²/log X` is what remains when `≍ log X` zeros stand at distance `≍ d` from `z`: then `R₂ ≍ log X/d²`. A cluster of `m`
zeros at distance `≍ d` gives `t ≍ d²/m`, in accordance with the sharp polynomial law.

Both conditions follow from the single first potential `R₁(z) = Σ_a m_a/|z − a|`: it suffices that `t (R₁(z) + log X) ≤ c d`
(`exists_zero_near_of_potential`), which also recovers the corpus bound `t log X ≤ c d²`, since `R₁ ≪ log X/d` always. If the packet has normal density around `z`, at most `A r log X` zeros within distance `r` at every
scale `r ≥ d`, then `R₁ ≪ A log X log(1/d)`, and the law reads `t A log X log(72/d) ≤ c d` (`exists_zero_near_of_normal_density`): linear in the depth, up to the logarithm.
-/

open Complex MeasureTheory Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The **zero energy** of a finite set of zeros of `H_t` at the point `z`. -/
def zeroEnergy (t : ℝ) (Z : Finset ℂ) (z : ℂ) : ℝ :=
  ∑ a ∈ Z, (zeroMult (riemannHeat t) a : ℝ) / ‖z - a‖ ^ 2

/-- The **first potential** of a finite set of zeros of `H_t` at the point `z`. -/
def zeroPotential (t : ℝ) (Z : Finset ℂ) (z : ℂ) : ℝ :=
  ∑ a ∈ Z, (zeroMult (riemannHeat t) a : ℝ) / ‖z - a‖

/-! ## The centered estimate with the exact zero energy -/

/-- Per-factor exponents add up over a product of powers. -/
theorem norm_prod_powers_sub_one_le_exp_sum {ι : Type*} {T : Finset ι} {m : ι → ℕ} {f : ι → ℂ} {K : ι → ℝ}
    (hf : ∀ a ∈ T, ‖f a - 1‖ ≤ Real.exp (K a) - 1) :
    ‖(∏ a ∈ T, f a ^ m a) - 1‖ ≤ Real.exp (∑ a ∈ T, (m a : ℝ) * K a) - 1 := by
  classical
  revert hf
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | @insert a T ha ih =>
    intro hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact norm_mul_sub_one_le_exp_add
      (norm_pow_sub_one_le_exp_mul (hf a (Finset.mem_insert_self a T)) (m a))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- **The centered factorization with the exact zero energy.** The segment may cross zeros; each one is charged only `2|u|²/|s − b|²`. -/
theorem norm_centered_factorization_sub_one_le_energy
    {T : Finset ℂ} {m : ℂ → ℕ} {f g : ℂ → ℂ} {s a : ℂ} {R K : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hg : Differentiable ℂ g)
    (hgne : ∀ w : ℂ, ‖w - s‖ ≤ 4 * R → g w ≠ 0)
    (hgq : ∀ w : ℂ, ‖w - s‖ ≤ 4 * R → ‖deriv (fun v => deriv g v / g v) w‖ ≤ K)
    (hfac : ∀ w : ℂ, f w = (∏ b ∈ T, (w - b) ^ m b) * g w) (hne : ∀ b ∈ T, s ≠ b)
    (ha : a = (∑ b ∈ T, (m b : ℂ) / (s - b)) + deriv g s / g s) {u : ℝ} (hu : |u| ≤ R) :
    ‖Complex.exp (-(u : ℂ) * a) * f (s + u) / f s - 1‖ ≤
      Real.exp ((2 * (∑ b ∈ T, (m b : ℝ) / ‖s - b‖ ^ 2) + K) * u ^ 2) - 1 := by
  have hP : (∏ b ∈ T, (s - b) ^ m b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b hb => pow_ne_zero _ (sub_ne_zero.mpr (hne b hb))
  have hgs : g s ≠ 0 := hgne s (by simpa only [sub_self, norm_zero] using (by positivity : 0 ≤ 4 * R))
  set p := ∑ b ∈ T, (m b : ℂ) / (s - b) with hp
  set q := deriv g s / g s with hq
  have hsplit : Complex.exp (-(u : ℂ) * a) * f (s + u) / f s =
      (Complex.exp (-((u : ℂ) * p)) *
        (∏ b ∈ T, (s + u - b) ^ m b) / (∏ b ∈ T, (s - b) ^ m b)) *
      (Complex.exp (-(u : ℂ) * q) * g (s + u) / g s) := by
    rw [ha, hfac (s + u), hfac s, mul_add, Complex.exp_add]
    rw [show -(u : ℂ) * p = -((u : ℂ) * p) by ring]
    field_simp [hP, hgs]
  have hpoly : ‖Complex.exp (-((u : ℂ) * p)) * (∏ b ∈ T, (s + u - b) ^ m b) / (∏ b ∈ T, (s - b) ^ m b) - 1‖ ≤
      Real.exp (2 * (∑ b ∈ T, (m b : ℝ) / ‖s - b‖ ^ 2) * u ^ 2) - 1 := by
    rw [hp, centered_root_product_eq hne]
    have hfactor : ∀ b ∈ T, ‖(1 + (u : ℂ) / (s - b)) * Complex.exp (-((u : ℂ) / (s - b))) - 1‖ ≤
        Real.exp (2 * u ^ 2 / ‖s - b‖ ^ 2) - 1 := by
      intro b _
      refine (norm_centered_linear_factor_sub_one_le _).trans (sub_le_sub_right (le_of_eq ?_) 1)
      congr 1
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    refine (norm_prod_powers_sub_one_le_exp_sum hfactor).trans (sub_le_sub_right (le_of_eq ?_) 1)
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcofactor := norm_exp_logDeriv_normalized_sub_one_le (z := s) (s := s)
    hR hK hg hgne hgq (by simp; positivity) hu
  rw [hsplit]
  have h := norm_mul_sub_one_le_exp_add hpoly hcofactor
  convert h using 1
  congr 2
  ring

/-- The multiplicity of a factor of a shifted factorization is the order of vanishing. -/
theorem zeroMult_eq_of_factorization {H g : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {c a : ℂ}
    (hH : Differentiable ℂ H) (hg : Differentiable ℂ g)
    (hfac : ∀ w : ℂ, H (c + w) = (∏ b ∈ T, (w - b) ^ m b) * g w) (ha : a ∈ T) (hga : g a ≠ 0) :
    zeroMult H (c + a) = m a := by
  classical
  have hHan : AnalyticAt ℂ H (c + a) := hH.analyticAt _
  have hord : analyticOrderAt H (c + a) = (m a : ℕ) := by
    rw [hHan.analyticOrderAt_eq_natCast]
    refine ⟨fun z => (∏ b ∈ T.erase a, (z - c - b) ^ m b) * g (z - c), ?_, ?_, ?_⟩
    · apply Differentiable.analyticAt
      refine Differentiable.mul ?_ (hg.comp (differentiable_id.sub_const c))
      exact Differentiable.fun_finsetProd fun b _ =>
        ((differentiable_id.sub_const c).sub_const b).pow _
    · beta_reduce
      rw [show c + a - c = a by ring]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun b hb => pow_ne_zero _ ?_) hga
      exact sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm
    · refine Eventually.of_forall fun z => ?_
      have h := hfac (z - c)
      rw [show c + (z - c) = z by ring, ← Finset.mul_prod_erase T _ ha] at h
      rw [h, smul_eq_mul, show z - (c + a) = z - c - a by ring]
      ring
  rw [zeroMult, hord]
  rfl

/-! ## The packet at a zero-free point -/

/-- **The local field and the local shape around a zero-free disc**, in terms of the potential and the energy at the centre. -/
theorem exists_packet_bounds :
    ∃ P : ℝ, 0 < P ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 →
      t * Real.log X ≤ 1 → ∀ (z : ℂ) (d : ℝ), z.re = X → |z.im| ≤ 1 / 2 → 0 < d → d ≤ 1 / 2 →
      (∀ ζ : ℂ, riemannHeat t ζ = 0 → d < ‖ζ - z‖) → ∀ Z : Finset ℂ,
      (∀ a : ℂ, riemannHeat t a = 0 → ‖a - ((X : ℂ) - 16 * I)‖ ≤ 18 → a ∈ Z) →
      ∀ s : ℂ, ‖s - z‖ ≤ d / 8 →
        ‖deriv (riemannHeat t) s / riemannHeat t s‖ ≤ 8 / 7 * zeroPotential t Z z + P * Real.log X ∧
        ∀ u : ℝ, |u| ≤ 1 / 32 →
          ‖Complex.exp (-(u : ℂ) * (deriv (riemannHeat t) s / riemannHeat t s)) *
              riemannHeat t (s + u) / riemannHeat t s - 1‖ ≤
            Real.exp ((2 * (64 / 49 * zeroEnergy t Z z) + P * Real.log X) * u ^ 2) - 1 := by
  classical
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_local_cofactor
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX t ht ht8 htL z d hzre hzim hd hd2 hno Z hZ s hs
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  have hCL : 0 < C * Real.log X := mul_pos hC hL
  obtain ⟨T₀, m, g, hg, hT₀, hgfree, hfac₀, -, hgq, hgq', -, -⟩ := hcofactor X hX t ht ht8 htL
  set T := T₀.filter (fun a => 0 < m a) with hT
  have hprod (w : ℂ) : (∏ a ∈ T, (w - a) ^ m a) = ∏ a ∈ T₀, (w - a) ^ m a := by
    rw [hT, Finset.prod_filter]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · have hm : m a = 0 := by omega
      simp only [hm, pow_zero]
  set c : ℂ := (X : ℂ) - 16 * I with hc
  set f : ℂ → ℂ := fun w => riemannHeat t (c + w) with hf
  have hfac (w : ℂ) : f w = (∏ a ∈ T, (w - a) ^ m a) * g w := by
    rw [hprod]
    exact hfac₀ w
  have hgdiff : Differentiable ℂ g := fun w => (hg w (mem_univ w)).differentiableAt
  have hHdiff := differentiable_riemannHeat ht
  have hderiv (w : ℂ) : deriv f w = deriv (riemannHeat t) (c + w) := by
    have h := (hHdiff (c + w)).hasDerivAt.comp w ((hasDerivAt_id w).const_add c)
    simpa only [Function.comp_def, mul_one] using h.deriv
  have hbase : ‖z - c‖ ≤ 33 / 2 := by
    have heq : z - c = ((z.im + 16 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hc, hzre]
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_add_le z.im 16
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h1
    linarith only [h1, hzim]
  have hsnear : ‖s - c‖ ≤ 33 / 2 + d / 8 := by
    calc ‖s - c‖ ≤ ‖s - z‖ + ‖z - c‖ := norm_sub_le_norm_sub_add_norm_sub s z c
      _ ≤ d / 8 + 33 / 2 := add_le_add hs hbase
      _ = _ := by ring
  have hs17 : ‖s - c‖ ≤ 17 := by linarith only [hsnear, hd2]
  have hTsub (a : ℂ) (ha : a ∈ T) : ‖a‖ ≤ 18 := hT₀ a (Finset.mem_filter.mp ha).1
  have hroot (a : ℂ) (ha : a ∈ T) : riemannHeat t (c + a) = 0 := by
    have hma : 0 < m a := (Finset.mem_filter.mp ha).2
    change f a = 0
    rw [hfac a]
    have hp : (∏ b ∈ T, (a - b) ^ m b) = 0 := by
      apply Finset.prod_eq_zero ha
      rw [sub_self, zero_pow (Nat.ne_of_gt hma)]
    rw [hp, zero_mul]
  have hmul (a : ℂ) (ha : a ∈ T) : zeroMult (riemannHeat t) (c + a) = m a :=
    zeroMult_eq_of_factorization hHdiff hgdiff hfac ha (hgfree a (hTsub a ha))
  have hsep (a : ℂ) (ha : a ∈ T) : d < ‖z - (c + a)‖ := by
    rw [norm_sub_rev]
    exact hno _ (hroot a ha)
  -- each pole is seen from `s` almost as from the centre
  have hfar (a : ℂ) (ha : a ∈ T) : 7 / 8 * ‖z - (c + a)‖ ≤ ‖s - c - a‖ := by
    have h1 := hsep a ha
    have h2 : ‖z - (c + a)‖ ≤ ‖s - c - a‖ + ‖s - z‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z s (c + a)
      rw [norm_sub_rev z s, show s - (c + a) = s - c - a by ring] at this
      linarith only [this]
    linarith only [h1, h2, hs]
  have hpos (a : ℂ) (ha : a ∈ T) : 0 < ‖z - (c + a)‖ := hd.trans (hsep a ha)
  have hne (a : ℂ) (ha : a ∈ T) : s - c ≠ a := by
    intro h
    have h1 := hfar a ha
    rw [h, sub_self, norm_zero] at h1
    have := hpos a ha
    linarith only [h1, this]
  -- transfer of sums to the packet `Z`
  have htransfer (F : ℂ → ℝ) (hF : ∀ w, 0 ≤ F w) :
      ∑ a ∈ T, (m a : ℝ) * F (c + a) ≤ ∑ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ) * F w := by
    have himg : T.image (fun a => c + a) ⊆ Z := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      refine hZ _ (hroot a ha) ?_
      rw [show c + a - ((X : ℂ) - 16 * I) = a by rw [hc]; ring]
      exact hTsub a ha
    calc ∑ a ∈ T, (m a : ℝ) * F (c + a)
        = ∑ w ∈ T.image (fun a => c + a), (zeroMult (riemannHeat t) w : ℝ) * F w := by
          rw [Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
          exact Finset.sum_congr rfl fun a ha => by rw [hmul a ha]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg fun w _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (hF w)
  have hscale : ‖s - c‖ < 18 := by linarith only [hs17]
  have hsc : c + (s - c) = s := by ring
  have hsplit := logDeriv_of_factor (f := f) (h := g) (U := ball 0 18) isOpen_ball
    hgdiff.differentiableOn
    (fun w hw => hgfree w (by simpa only [sub_zero] using (mem_ball_iff_norm.mp hw).le))
    (fun w _ => hfac w)
    (by simpa only [mem_ball_iff_norm, sub_zero] using hscale) hne
  rw [logDeriv_apply, logDeriv_apply, hderiv, hsc] at hsplit
  simp only [hf, hsc] at hsplit
  change deriv (riemannHeat t) s / riemannHeat t s =
    (∑ a ∈ T, (m a : ℂ) / (s - c - a)) + deriv g (s - c) / g (s - c) at hsplit
  constructor
  · -- the field
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hgq (s - c) hs17))
    have h1 : ‖∑ a ∈ T, (m a : ℂ) / (s - c - a)‖ ≤ ∑ a ∈ T, (m a : ℝ) * (8 / 7 * (‖z - (c + a)‖)⁻¹) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
      rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have h2 := hfar a ha
      have h3 := hpos a ha
      rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) h2) (by positivity)]
      refine le_trans (le_of_eq ?_) h2
      field_simp
    refine h1.trans ?_
    have h2 := htransfer (fun w => 8 / 7 * (‖z - w‖)⁻¹) fun w => by positivity
    refine h2.trans (le_of_eq ?_)
    rw [zeroPotential, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [div_eq_mul_inv]
    ring
  · -- the shape
    intro u hu
    have hcofree : ∀ w : ℂ, ‖w - (s - c)‖ ≤ 4 * (1 / 32 : ℝ) → g w ≠ 0 := by
      intro w hw
      have htri := norm_le_norm_sub_add w (s - c)
      apply hgfree w
      linarith only [htri, hw, hsnear, hd2]
    have hcoq : ∀ w : ℂ, ‖w - (s - c)‖ ≤ 4 * (1 / 32 : ℝ) →
        ‖deriv (fun v => deriv g v / g v) w‖ ≤ C * Real.log X := by
      intro w hw
      have htri := norm_le_norm_sub_add w (s - c)
      apply hgq' w
      linarith only [htri, hw, hsnear, hd2]
    have herror := norm_centered_factorization_sub_one_le_energy
      (s := s - c) (a := deriv (riemannHeat t) s / riemannHeat t s)
      (by norm_num : (0 : ℝ) < 1 / 32) hCL hgdiff hcofree hcoq hfac hne hsplit hu
    have hshift : f (s - c + u) = riemannHeat t (s + u) := by
      simp only [hf]
      congr 1
      ring
    rw [hshift, show f (s - c) = riemannHeat t s by simp only [hf, hsc]] at herror
    refine herror.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg u)
    have h1 : ∑ b ∈ T, (m b : ℝ) / ‖s - c - b‖ ^ 2 ≤
        ∑ b ∈ T, (m b : ℝ) * (64 / 49 * (‖z - (c + b)‖ ^ 2)⁻¹) := by
      refine Finset.sum_le_sum fun a ha => ?_
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have h2 := hfar a ha
      have h3 := hpos a ha
      have h4 : (7 / 8 * ‖z - (c + a)‖) ^ 2 ≤ ‖s - c - a‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      have h5 : 0 < (7 / 8 * ‖z - (c + a)‖) ^ 2 := by positivity
      rw [inv_le_comm₀ (lt_of_lt_of_le h5 h4) (by positivity)]
      refine le_trans (le_of_eq ?_) h4
      field_simp
      norm_num
    have h2 := htransfer (fun w => 64 / 49 * (‖z - w‖ ^ 2)⁻¹) fun w => by positivity
    have h3 : ∑ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ) * (64 / 49 * (‖z - w‖ ^ 2)⁻¹) =
        64 / 49 * zeroEnergy t Z z := by
      rw [zeroEnergy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [div_eq_mul_inv]
      ring
    rw [h3] at h2
    linarith only [h1, h2]

/-- The normalized heat function grows at most exponentially on real lines. -/
theorem norm_normalized_heat_le {t X A B G : ℝ} {s a : ℂ}
    (hL : 1 ≤ Real.log X) (hG : 0 ≤ G)
    (hsre : |s.re - X| ≤ 1) (hsim : |s.im| ≤ 1)
    (hs : ‖xiLine X 16‖ / 8 * Real.exp (-(A * Real.log X)) ≤ ‖riemannHeat t s‖)
    (ha : ‖a‖ ≤ B * Real.log X)
    (hg : ∀ x y : ℝ, |y| ≤ 1 → ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      ‖xiLine X 16‖ * Real.exp (G * Real.log X * (1 + |x - X|))) (u : ℝ) :
    ‖Complex.exp (-(u : ℂ) * a) * riemannHeat t (s + u) / riemannHeat t s‖ ≤
      Real.exp ((8 + 2 * G + A) * Real.log X + (B + G) * Real.log X * |u|) := by
  set N := ‖xiLine X 16‖ with hNdef
  have hN : 0 < N := by
    apply norm_pos_iff.mpr
    apply xi_ne_zero_of_one_lt_re
    norm_num [xiLine]
  have hmin : 0 < N / 8 * Real.exp (-(A * Real.log X)) := by positivity
  have hnorm : 0 < ‖riemannHeat t s‖ := hmin.trans_le hs
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hphase : ‖Complex.exp (-(u : ℂ) * a)‖ ≤ Real.exp (B * Real.log X * |u|) := by
    have hneg : -(u * a.re) ≤ |u| * (B * Real.log X) := by
      calc
        _ ≤ |u * a.re| := neg_le_abs _
        _ = |u| * |a.re| := abs_mul _ _
        _ ≤ |u| * ‖a‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm a) (abs_nonneg u)
        _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg u)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(u : ℂ) * a).re = -(u * a.re) := by simp
    rw [hre]
    nlinarith only [hneg]
  have hshift : |(s + (u : ℂ)).re - X| ≤ 1 + |u| := by
    rw [Complex.add_re, Complex.ofReal_re, show s.re + u - X = (s.re - X) + u by ring]
    exact (abs_add_le _ _).trans (add_le_add hsre le_rfl)
  have hpoint : ((s + (u : ℂ)).re : ℂ) + I * (s + (u : ℂ)).im = s + u := by
    simpa only [mul_comm I] using Complex.re_add_im (s + (u : ℂ))
  have hheat : ‖riemannHeat t (s + u)‖ ≤ N * Real.exp (G * Real.log X * (2 + |u|)) := by
    have h := hg (s + (u : ℂ)).re (s + (u : ℂ)).im (by simpa using hsim)
    rw [hpoint] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    have hb := mul_le_mul_of_nonneg_left hshift (mul_nonneg hG hL0)
    nlinarith only [hb]
  have height : (8 : ℝ) ≤ Real.exp (8 * Real.log X) := by
    linarith only [Real.add_one_le_exp (8 * Real.log X), hL]
  rw [norm_div, norm_mul]
  calc
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (G * Real.log X * (2 + |u|)))) / ‖riemannHeat t s‖ :=
      div_le_div_of_nonneg_right (mul_le_mul hphase hheat (norm_nonneg _) (Real.exp_pos _).le)
        hnorm.le
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (G * Real.log X * (2 + |u|)))) /
          (N / 8 * Real.exp (-(A * Real.log X))) :=
      div_le_div_of_nonneg_left (by positivity) hmin hs
    _ = 8 * Real.exp (B * Real.log X * |u| + G * Real.log X * (2 + |u|) + A * Real.log X) := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_add]
      field_simp [hN.ne']
    _ ≤ Real.exp (8 * Real.log X) *
        Real.exp (B * Real.log X * |u| + G * Real.log X * (2 + |u|) + A * Real.log X) :=
      mul_le_mul_of_nonneg_right height (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ## The depth law -/

/-- **The depth law with its crowd.** A zero `z` of `H_{t₀}` has a zero of `H_{t₀+t}` within distance `d`, as soon as `t log X ≤ c d`, the field of `H_{t₀+t}` near `z`
satisfies `t|V| ≤ c d`, and its zero energy at `z` satisfies `t R₂(z) ≤ c`. -/
theorem exists_zero_near_of_no_crowd :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ t₀ t : ℝ, 0 ≤ t₀ → 0 < t → (t₀ + t) * Real.log X ≤ 1 → t * Real.log X ≤ c * d →
      ∀ z : ℂ, z.re = X → |z.im| ≤ 1 / 2 → riemannHeat t₀ z = 0 →
      ∀ (Z : Finset ℂ) (V : ℝ),
        (∀ a : ℂ, riemannHeat (t₀ + t) a = 0 → ‖a - ((X : ℂ) - 16 * I)‖ ≤ 18 → a ∈ Z) →
        t * V ≤ c * d → t * zeroEnergy (t₀ + t) Z z ≤ c →
        (∀ s : ℂ, ‖s - z‖ ≤ d / 8 → riemannHeat (t₀ + t) s ≠ 0 →
          ‖deriv (riemannHeat (t₀ + t)) s / riemannHeat (t₀ + t) s‖ ≤ V) →
        ∃ ζ : ℂ, riemannHeat (t₀ + t) ζ = 0 ∧ ‖ζ - z‖ ≤ d := by
  obtain ⟨G, hG, X₁, hX₁, hglobal⟩ := exists_riemannHeat_global_relative_bound
  obtain ⟨C, hC, X₂, hX₂, hwindow⟩ := exists_riemannHeat_shrinking_window_bounds
  obtain ⟨P, hP, X₃, hX₃, hpacket⟩ := exists_packet_bounds
  set R : ℝ := 1 / 32 with hRdef
  have hR : 0 < R := by norm_num [hRdef]
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  set M := 8 + 2 * G + C + Real.log 32 with hMdef
  set D₀ := C + G with hD₀def
  have hM : 0 < M := by positivity
  have hD₀ : 0 < D₀ := by positivity
  set c := min (1 / 336) (min (1 / (64 * P)) (min (R / (8 * D₀)) (R ^ 2 / (8 * M)))) with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  have hc_all := (le_refl c)
  rw [hcdef] at hc_all
  simp only [le_min_iff] at hc_all
  rw [← hcdef] at hc_all
  obtain ⟨hc1, hcP, hct, hce⟩ := hc_all
  refine ⟨c, hc, X₁ + X₂ + X₃ + Real.exp 20, by linarith only [hX₁, hX₂, hX₃, Real.exp_pos 20], ?_⟩
  intro X hX₀ d hd hd2 t₀ t ht₀ ht htX htc z hzre hzim hz0 Z V hZ htV htE hV
  have hX1 : X₁ ≤ X := by linarith only [hX₀, hX₂, hX₃, hX₂, hX₃, hX₁, Real.exp_pos 20]
  have hX2 : X₂ ≤ X := by linarith only [hX₀, hX₁, hX₃, hX₂, hX₃, hX₁, Real.exp_pos 20]
  have hX3 : X₃ ≤ X := by linarith only [hX₀, hX₁, hX₂, hX₂, hX₃, hX₁, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20)
      (show Real.exp 20 ≤ X by linarith only [hX₀, hX₁, hX₂, hX₃])
    simpa only [Real.log_exp] using h
  have hL0 : 0 < Real.log X := by linarith only [hL]
  have hd1 : d ≤ 1 := by linarith only [hd2]
  set t₁ := t₀ + t with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁8 : t₁ ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hL ht₁0.le
    nlinarith only [h, htX]
  by_contra hcon
  push Not at hcon
  have hno : ∀ ζ : ℂ, riemannHeat t₁ ζ = 0 → d < ‖ζ - z‖ := hcon
  rcases hwindow X hX2 t₁ ht₁0.le ht₁8 htX d hd hd2 z hzre hzim with hzero | hb
  · obtain ⟨ζ, hζ, hle⟩ := hzero
    exact absurd (hno ζ hζ) (not_lt.mpr hle)
  set r := d / 32 with hrdef
  have hr : 0 < r := by positivity
  have hsaddle : 2 * t * V ≤ r := by
    have h1 := mul_le_mul_of_nonneg_right hc1 hd.le
    rw [hrdef]
    nlinarith only [htV, h1, hd]
  have hdiff := differentiable_riemannHeat ht₁0.le
  have hin (w : ℂ) (hw : w ∈ ball z (2 * r)) : ‖w - z‖ ≤ d / 8 := by
    have h := mem_ball_iff_norm.mp hw
    rw [hrdef] at h
    linarith only [h, hd]
  obtain ⟨s, hs, hseq⟩ := exists_logDeriv_saddle (f := riemannHeat t₁) (z := z)
    hr ht.le hsaddle hdiff.differentiableOn (fun w hw => (hb w (hin w hw)).1)
    (fun w hw => hV w (hin w hw) (hb w (hin w hw)).1)
  have hs8 : ‖s - z‖ ≤ d / 8 := by
    rw [hrdef] at hs
    linarith only [hs, hd]
  obtain ⟨hsne, ha₀, hfloor, -⟩ := hb s hs8
  set a := deriv (riemannHeat t₁) s / riemannHeat t₁ s with hadef
  have hsa : s = z + 2 * (t : ℂ) * a := hseq
  set F : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ) * a) * riemannHeat t₁ (s + u) / riemannHeat t₁ s with hFdef
  have hF : Continuous F := by
    have hcont := hdiff.continuous
    simp only [hFdef]
    fun_prop
  set E := 8 + 2 * G + C / d with hEdef
  set D := C / d + G with hDdef
  have hE : 0 < E := by positivity
  have hDpos : 0 < D := by positivity
  have hdD : d * D ≤ D₀ := by
    have he : d * D = C + G * d := by
      rw [hDdef]
      field_simp
    rw [he, hD₀def]
    have := mul_le_mul_of_nonneg_left hd1 hG.le
    linarith only [this]
  have hdE : d * (E + Real.log 32) ≤ M := by
    have he : d * (E + Real.log 32) = (8 + 2 * G + Real.log 32) * d + C := by
      rw [hEdef]
      field_simp
      ring
    rw [he, hMdef]
    have hB : 0 ≤ 8 + 2 * G + Real.log 32 := by positivity
    have := mul_le_mul_of_nonneg_left hd1 hB
    linarith only [this]
  have htD : t * (D * Real.log X) ≤ R / 8 := by
    have h1 := mul_le_mul_of_nonneg_right htc hDpos.le
    have h2 := mul_le_mul_of_nonneg_left hdD hc.le
    have h3 := (le_div_iff₀ (by positivity : 0 < 8 * D₀)).mp hct
    calc t * (D * Real.log X) = t * Real.log X * D := by ring
      _ ≤ c * d * D := h1
      _ = c * (d * D) := by ring
      _ ≤ c * D₀ := h2
      _ ≤ R / 8 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        calc c * D₀ * 8 = c * (8 * D₀) := by ring
          _ ≤ R := h3
  have htE' : t * Real.log X * (E + Real.log 32) ≤ R ^ 2 / 8 := by
    have h1 := mul_le_mul_of_nonneg_right htc (show 0 ≤ E + Real.log 32 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hdE hc.le
    have h3 := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp hce
    calc t * Real.log X * (E + Real.log 32) ≤ c * d * (E + Real.log 32) := h1
      _ = c * (d * (E + Real.log 32)) := by ring
      _ ≤ c * M := h2
      _ ≤ R ^ 2 / 8 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        calc c * M * 8 = c * (8 * M) := by ring
          _ ≤ R ^ 2 := h3
  have hsre : |s.re - X| ≤ 1 := by
    have h := Complex.abs_re_le_norm (s - z)
    rw [Complex.sub_re, hzre] at h
    linarith only [h, hs8, hd2]
  have hsim : |s.im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (s - z)
    rw [Complex.sub_im] at h
    have htri : |s.im| ≤ |s.im - z.im| + |z.im| := by
      simpa only [sub_add_cancel] using abs_add_le (s.im - z.im) z.im
    linarith only [h, hs8, htri, hzim, hd2]
  have hA : (C / d) * Real.log X = C * Real.log X / d := by ring
  have henv : ∀ u : ℝ, ‖F u‖ ≤ Real.exp (E * Real.log X + (D * Real.log X) * |u|) := by
    intro u
    exact norm_normalized_heat_le (A := C / d) (B := C / d)
      (by linarith only [hL]) hG.le hsre hsim
      (by rw [hA]; exact hfloor) (by rw [hA]; exact ha₀)
      (hglobal X hX1 t₁ ht₁0.le ht₁8 htX) u
  -- the quadratic constant
  set W := zeroEnergy t₁ Z z with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun a _ => by positivity
  set K := 2 * (64 / 49 * W) + P * Real.log X with hKdef
  have hK0 : 0 ≤ K := by positivity
  have htK : t * K ≤ 1 / 64 := by
    have h1 : t * (P * Real.log X) ≤ 1 / 128 := by
      have h2 := mul_le_mul_of_nonneg_left htc hP.le
      have h3 := (le_div_iff₀ (by positivity : 0 < 64 * P)).mp hcP
      have h4 : c * d ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left hd2 hc.le
      have h5 := mul_le_mul_of_nonneg_left h4 hP.le
      nlinarith only [h2, h3, h5]
    have h2 : t * (2 * (64 / 49 * W)) ≤ 1 / 128 := by
      have : t * (2 * (64 / 49 * W)) = 128 / 49 * (t * W) := by ring
      rw [this]
      linarith only [htE, hc1]
    rw [hKdef, mul_add]
    linarith only [h1, h2]
  have hlocal : ∀ u : ℝ, |u| ≤ R → ‖F u - 1‖ ≤ Real.exp (K * u ^ 2) - 1 := fun u hu =>
    (hpacket X hX3 t₁ ht₁0.le ht₁8 htX z d hzre hzim hd hd2 hno Z hZ s hs8).2 u hu
  obtain ⟨-, herr⟩ := integral_gaussDensity_quadratic_error_le ht hR hK0
    (mul_nonneg hE.le hL0.le) (mul_nonneg hDpos.le hL0.le)
    (by linarith only [htK]) htD hF hlocal henv
  have htail : Real.exp (E * Real.log X - R ^ 2 / (8 * t)) ≤ (1 / 32 : ℝ) := by
    have hpaid : Real.log X * (E + Real.log 32) ≤ R ^ 2 / (8 * t) := by
      rw [le_div_iff₀ (by positivity : 0 < 8 * t)]
      calc
        _ = (t * Real.log X * (E + Real.log 32)) * 8 := by ring
        _ ≤ (R ^ 2 / 8) * 8 := mul_le_mul_of_nonneg_right htE' (by norm_num)
        _ = _ := by ring
    have hlog := mul_le_mul_of_nonneg_left (show 1 ≤ Real.log X by linarith only [hL]) hlog32
    calc
      _ ≤ Real.exp (-Real.log 32) := Real.exp_le_exp.mpr (by nlinarith only [hpaid, hlog])
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hsmall : ‖(∫ u : ℝ, (gaussDensity t u : ℂ) * F u) - 1‖ ≤ 1 / 2 := by
    nlinarith only [herr, htK, htail]
  have hI : (∫ u : ℝ, (gaussDensity t u : ℂ) * F u) ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, norm_neg, norm_one] at hsmall
    norm_num at hsmall
  have hreverse := riemannHeat_sub_eq_reverse_saddle ht₁0.le ht z a
  rw [ht₁, add_sub_cancel_right, ← ht₁, ← hsa] at hreverse
  have hint : (∫ u : ℝ, (gaussDensity t u : ℂ) * Complex.exp (-(u : ℂ) * a) * riemannHeat t₁ (s + u)) =
      (∫ u : ℝ, (gaussDensity t u : ℂ) * F u) * riemannHeat t₁ s := by
    rw [← integral_mul_const]
    congr 1
    funext u
    simp only [hFdef]
    field_simp [hsne]
  rw [hint, hz0] at hreverse
  exact (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hI hsne)) hreverse.symm

/-- **The depth law with the first potential.** A zero `z` of `H_{t₀}` has a zero of `H_{t₀+t}` within distance `d` as soon as `t (R₁(z) + log X) ≤ c d`. -/
theorem exists_zero_near_of_potential :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ t₀ t : ℝ, 0 ≤ t₀ → 0 < t → (t₀ + t) * Real.log X ≤ 1 →
      ∀ z : ℂ, z.re = X → |z.im| ≤ 1 / 2 → riemannHeat t₀ z = 0 →
      ∀ Z : Finset ℂ, (∀ a : ℂ, riemannHeat (t₀ + t) a = 0 → ‖a - ((X : ℂ) - 16 * I)‖ ≤ 18 → a ∈ Z) →
        t * (zeroPotential (t₀ + t) Z z + Real.log X) ≤ c * d →
        ∃ ζ : ℂ, riemannHeat (t₀ + t) ζ = 0 ∧ ‖ζ - z‖ ≤ d := by
  obtain ⟨c, hc, X₁, hX₁, hdepth⟩ := exists_zero_near_of_no_crowd
  obtain ⟨P, hP, X₂, hX₂, hpacket⟩ := exists_packet_bounds
  set c' := min c (c / (2 + P)) with hc'def
  have hc' : 0 < c' := by
    rw [hc'def]
    positivity
  have hc'1 : c' ≤ c := min_le_left _ _
  have hc'2 : c' ≤ c / (2 + P) := min_le_right _ _
  refine ⟨c', hc', X₁ + X₂ + Real.exp 20, by linarith only [hX₁, hX₂, Real.exp_pos 20], ?_⟩
  intro X hX₀ d hd hd2 t₀ t ht₀ ht htX z hzre hzim hz0 Z hZ hpot
  have hXa : X₁ ≤ X := by linarith only [hX₀, hX₂, hX₁, Real.exp_pos 20]
  have hXb : X₂ ≤ X := by linarith only [hX₀, hX₁, hX₂, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20)
      (show Real.exp 20 ≤ X by linarith only [hX₀, hX₁, hX₂])
    simpa only [Real.log_exp] using h
  have hL0 : 0 < Real.log X := by linarith only [hL]
  set t₁ := t₀ + t with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁8 : t₁ ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hL ht₁0.le
    nlinarith only [h, htX]
  set R₁ := zeroPotential t₁ Z z with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun a _ => by positivity
  by_contra hcon
  push Not at hcon
  have hno : ∀ ζ : ℂ, riemannHeat t₁ ζ = 0 → d < ‖ζ - z‖ := hcon
  have hcd : t * (R₁ + Real.log X) ≤ c' * d := hpot
  have hc'd : c' * d ≤ c * d := mul_le_mul_of_nonneg_right hc'1 hd.le
  have htL : t * Real.log X ≤ c * d := by
    have : 0 ≤ t * R₁ := by positivity
    rw [mul_add] at hcd
    linarith only [this, hcd, hc'd]
  set V := 8 / 7 * R₁ + P * Real.log X with hVdef
  have htV : t * V ≤ c * d := by
    have h1 : t * V ≤ (2 + P) * (t * (R₁ + Real.log X)) := by
      rw [hVdef]
      have h2 : 0 ≤ t * R₁ := by positivity
      have h3 : 0 ≤ t * Real.log X := by positivity
      have h4 : 0 ≤ P * (t * R₁) := by positivity
      nlinarith only [h2, h3, h4]
    have h2 := mul_le_mul_of_nonneg_left hcd (by positivity : 0 ≤ 2 + P)
    have h3 := (le_div_iff₀ (by positivity : 0 < 2 + P)).mp hc'2
    have h4 := mul_le_mul_of_nonneg_right h3 hd.le
    nlinarith only [h1, h2, h4]
  -- the energy is paid by the potential, the zeros being at distance at least `d`
  have hEn : d * zeroEnergy t₁ Z z ≤ R₁ := by
    rw [zeroEnergy, Finset.mul_sum, hR₁, zeroPotential]
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases ha : riemannHeat t₁ a = 0
    · have h1 : d < ‖z - a‖ := by
        rw [norm_sub_rev]
        exact hno a ha
      have h2 : 0 < ‖z - a‖ := hd.trans h1
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) h2]
      have h3 : (0 : ℝ) ≤ zeroMult (riemannHeat t₁) a := Nat.cast_nonneg _
      have h4 := mul_le_mul_of_nonneg_left h1.le (mul_nonneg h3 h2.le)
      nlinarith only [h4]
    · have h0 : zeroMult (riemannHeat t₁) a = 0 := by
        rw [zeroMult]
        have hord : analyticOrderAt (riemannHeat t₁) a = 0 :=
          ((differentiable_riemannHeat ht₁0.le).analyticAt a).analyticOrderAt_eq_zero.mpr ha
        rw [hord]
        rfl
      simp [h0]
  have htEn : t * zeroEnergy t₁ Z z ≤ c := by
    have h1 : t * (d * zeroEnergy t₁ Z z) ≤ t * R₁ := mul_le_mul_of_nonneg_left hEn ht.le
    have h2 : t * R₁ ≤ c * d := by
      have : 0 ≤ t * Real.log X := by positivity
      rw [mul_add] at hcd
      linarith only [this, hcd, hc'd]
    have h3 : d * (t * zeroEnergy t₁ Z z) ≤ d * c := by
      calc d * (t * zeroEnergy t₁ Z z) = t * (d * zeroEnergy t₁ Z z) := by ring
        _ ≤ d * c := by linarith only [h1, h2]
    exact le_of_mul_le_mul_left h3 hd
  obtain ⟨ζ, hζ, hle⟩ := hdepth X hXa d hd hd2 t₀ t ht₀ ht htX htL z hzre hzim hz0 Z V hZ htV htEn
    (fun s hs _ => (hpacket X hXb t₁ ht₁0.le ht₁8 htX z d hzre hzim hd hd2 hno Z hZ s hs).1)
  exact absurd (hno ζ hζ) (not_lt.mpr hle)

/-- A nonreal zero of `H_{t₀}` at depth at least `d` keeps a nonreal zero of `H_{t₀+t}` at distance at most `d/2`, as soon as `t (R₁(z) + log X) ≤ c d`. -/
theorem exists_nonreal_zero_near_of_potential :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ t₀ t : ℝ, 0 ≤ t₀ → 0 < t → (t₀ + t) * Real.log X ≤ 1 →
      ∀ z : ℂ, z.re = X → d ≤ |z.im| → |z.im| ≤ 1 / 2 → riemannHeat t₀ z = 0 →
      ∀ Z : Finset ℂ, (∀ a : ℂ, riemannHeat (t₀ + t) a = 0 → ‖a - ((X : ℂ) - 16 * I)‖ ≤ 18 → a ∈ Z) →
        t * (zeroPotential (t₀ + t) Z z + Real.log X) ≤ c * d →
        ∃ ζ : ℂ, riemannHeat (t₀ + t) ζ = 0 ∧ ζ.im ≠ 0 ∧ ‖ζ - z‖ ≤ d / 2 := by
  obtain ⟨c, hc, X₀, hX₀, hnear⟩ := exists_zero_near_of_potential
  refine ⟨c / 2, by positivity, X₀, hX₀, ?_⟩
  intro X hX d hd hd2 t₀ t ht₀ ht htX z hzre hzd hzim hz0 Z hZ hpot
  obtain ⟨ζ, hζ, hle⟩ := hnear X hX (d / 2) (by positivity) (by linarith only [hd2]) t₀ t ht₀ ht htX
    z hzre hzim hz0 Z hZ (by linarith only [hpot])
  refine ⟨ζ, hζ, ?_, hle⟩
  intro him
  have h := Complex.abs_im_le_norm (ζ - z)
  rw [Complex.sub_im, him, zero_sub, abs_neg] at h
  linarith only [h, hle, hzd, hd]

/-- **The potential of a packet of normal density.** If all zeros are at distance more than `d` from `z`, and at most `A r L` of them within distance `r` for `r ≥ d`, then the zeros within distance `2^K d` contribute at most `2 A L K` to the potential. -/
theorem sum_potential_le_of_normal {t d A L : ℝ} {z : ℂ} {Z : Finset ℂ} (hd : 0 < d)
    (hfar : ∀ a ∈ Z, zeroMult (riemannHeat t) a ≠ 0 → d < ‖z - a‖)
    (hcount : ∀ r : ℝ, d ≤ r → (∑ a ∈ Z.filter (fun a => ‖z - a‖ ≤ r), (zeroMult (riemannHeat t) a : ℝ)) ≤ A * r * L)
    (K : ℕ) :
    ∑ a ∈ Z.filter (fun a => ‖z - a‖ ≤ 2 ^ K * d), (zeroMult (riemannHeat t) a : ℝ) / ‖z - a‖ ≤
      2 * A * L * K := by
  classical
  induction K with
  | zero =>
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero]
    refine Finset.sum_nonpos fun a ha => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
    by_cases hm : zeroMult (riemannHeat t) a = 0
    · simp [hm]
    · exact absurd (hfar a h1 hm) (not_lt.mpr h2)
  | succ K ih =>
    have hpow : (0 : ℝ) < 2 ^ K * d := by positivity
    have hge : d ≤ 2 ^ (K + 1) * d := by
      have h1 : (1 : ℝ) ≤ 2 ^ (K + 1) := one_le_pow₀ (by norm_num)
      nlinarith only [h1, hd]
    set B₁ := Z.filter (fun a => ‖z - a‖ ≤ 2 ^ K * d) with hB₁
    set B₂ := Z.filter (fun a => ‖z - a‖ ≤ 2 ^ (K + 1) * d) with hB₂
    have hsub : B₁ ⊆ B₂ := by
      intro a ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨h1, h2.trans ?_⟩
      rw [pow_succ]
      nlinarith only [hpow]
    have hshell : ∑ a ∈ B₂ \ B₁, (zeroMult (riemannHeat t) a : ℝ) / ‖z - a‖ ≤ 2 * A * L := by
      have h1 : ∑ a ∈ B₂ \ B₁, (zeroMult (riemannHeat t) a : ℝ) / ‖z - a‖ ≤
          ∑ a ∈ B₂ \ B₁, (zeroMult (riemannHeat t) a : ℝ) / (2 ^ K * d) := by
        refine Finset.sum_le_sum fun a ha => ?_
        obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp ha
        have h4 : 2 ^ K * d < ‖z - a‖ := by
          by_contra hn
          exact h3 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h2).1, not_lt.mp hn⟩)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpow h4.le
      refine h1.trans ?_
      rw [← Finset.sum_div, div_le_iff₀ hpow]
      have h5 : ∑ a ∈ B₂ \ B₁, (zeroMult (riemannHeat t) a : ℝ) ≤ ∑ a ∈ B₂, (zeroMult (riemannHeat t) a : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _
      refine (h5.trans (hcount _ hge)).trans (le_of_eq ?_)
      rw [pow_succ]
      ring
    rw [← Finset.sum_sdiff hsub]
    push_cast
    linarith only [hshell, ih]

/-- **The depth law at normal density.** If at most `A r log X` zeros of `H_{t₀+t}` lie within distance `r` of a zero `z` of `H_{t₀}`, at every scale `r ≥ d`, then `H_{t₀+t}` has a zero within distance `d` of `z` as soon as
`t A log X log(72/d) ≤ c d`. -/
theorem exists_zero_near_of_normal_density :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ∀ t₀ t : ℝ, 0 ≤ t₀ → 0 < t → (t₀ + t) * Real.log X ≤ 1 →
      ∀ z : ℂ, z.re = X → |z.im| ≤ 1 / 2 → riemannHeat t₀ z = 0 →
      ∀ (Z : Finset ℂ) (A : ℝ), 1 ≤ A →
        (∀ a : ℂ, riemannHeat (t₀ + t) a = 0 → ‖a - ((X : ℂ) - 16 * I)‖ ≤ 18 → a ∈ Z) →
        (∀ a ∈ Z, ‖z - a‖ ≤ 36) →
        (∀ r : ℝ, d ≤ r → (∑ a ∈ Z.filter (fun a => ‖z - a‖ ≤ r),
          (zeroMult (riemannHeat (t₀ + t)) a : ℝ)) ≤ A * r * Real.log X) →
        t * (A * Real.log X * Real.log (72 / d)) ≤ c * d →
        ∃ ζ : ℂ, riemannHeat (t₀ + t) ζ = 0 ∧ ‖ζ - z‖ ≤ d := by
  obtain ⟨c, hc, X₀, hX₀, hpot⟩ := exists_zero_near_of_potential
  refine ⟨c / 8, by positivity, X₀, hX₀, ?_⟩
  intro X hX d hd hd2 t₀ t ht₀ ht htX z hzre hzim hz0 Z A hA hZ hZ36 hcount hsmall
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  set t₁ := t₀ + t with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  by_contra hcon
  push Not at hcon
  have hno : ∀ ζ : ℂ, riemannHeat t₁ ζ = 0 → d < ‖ζ - z‖ := hcon
  have hfar : ∀ a ∈ Z, zeroMult (riemannHeat t₁) a ≠ 0 → d < ‖z - a‖ := by
    intro a _ hm
    by_cases ha : riemannHeat t₁ a = 0
    · rw [norm_sub_rev]
      exact hno a ha
    · exfalso
      apply hm
      rw [zeroMult]
      have hord : analyticOrderAt (riemannHeat t₁) a = 0 :=
        ((differentiable_riemannHeat ht₁0.le).analyticAt a).analyticOrderAt_eq_zero.mpr ha
      rw [hord]
      rfl
  -- the number of dyadic scales
  set l := Real.log (72 / d) with hl
  have h72 : 1 < 72 / d := by
    rw [lt_div_iff₀ hd]
    linarith only [hd2]
  have hl0 : 0 < l := Real.log_pos h72
  have hl1 : 1 ≤ l := by
    have h1 : Real.exp 1 ≤ 72 / d := by
      rw [le_div_iff₀ hd]
      have h2 := Real.exp_one_lt_d9
      nlinarith only [h2, hd2, hd, Real.exp_pos 1]
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  set K := Nat.ceil (2 * l) with hKdef
  have hK1 : 2 * l ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 3 * l := by
    have := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * l)).le
    linarith only [this, hl1]
  have hpow : 72 / d ≤ 2 ^ K := by
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith only [this]
    have h1 : l ≤ K * Real.log 2 := by
      have h2 : 2 * l * (1 / 2) ≤ K * Real.log 2 :=
        mul_le_mul hK1 hlog2 (by norm_num) (Nat.cast_nonneg _)
      linarith only [h2]
    have h3 : Real.exp l ≤ Real.exp (K * Real.log 2) := Real.exp_le_exp.mpr h1
    rw [hl, Real.exp_log (by positivity), mul_comm, Real.exp_mul, Real.exp_log (by norm_num),
      Real.rpow_natCast] at h3
    exact h3
  have hall : Z.filter (fun a => ‖z - a‖ ≤ 2 ^ K * d) = Z := by
    refine Finset.filter_true_of_mem fun a ha => (hZ36 a ha).trans ?_
    have h1 := (div_le_iff₀ hd).mp hpow
    linarith only [h1]
  have hR := sum_potential_le_of_normal hd hfar hcount K
  rw [hall] at hR
  have hRle : zeroPotential t₁ Z z ≤ 6 * A * Real.log X * l := by
    have h1 : 2 * A * Real.log X * K ≤ 2 * A * Real.log X * (3 * l) :=
      mul_le_mul_of_nonneg_left hK2 (by positivity)
    unfold zeroPotential
    linarith only [hR, h1]
  have hineq : t * (zeroPotential t₁ Z z + Real.log X) ≤ c * d := by
    have h1 : Real.log X ≤ A * Real.log X * l := by
      have h2 : 1 ≤ A * l := by nlinarith only [hA, hl1]
      nlinarith only [h2, hL]
    have h2 : zeroPotential t₁ Z z + Real.log X ≤ 7 * (A * Real.log X * l) := by
      linarith only [hRle, h1]
    have h3 := mul_le_mul_of_nonneg_left h2 ht.le
    have h4 : t * (7 * (A * Real.log X * l)) = 7 * (t * (A * Real.log X * l)) := by ring
    have h5 : 0 ≤ c * d := by positivity
    linarith only [h3, h4, hsmall, h5]
  obtain ⟨ζ, hζ, hle⟩ := hpot X hX d hd hd2 t₀ t ht₀ ht htX z hzre hzim hz0 Z hZ hineq
  exact absurd (hno ζ hζ) (not_lt.mpr hle)

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
