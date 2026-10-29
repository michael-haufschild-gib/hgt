import GaloisForLFunctions.RHTower.HeatLocalCofactor
import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.RHTower.DeBruijnStripThreshold
import GaloisForLFunctions.RHTower.XiExceptionalPointDiscrete
import GaloisForLFunctions.HTGeometry.LogDerivativeFactor

/-!
# The exterior force on a local packet of heat zeros

Extracting all zeros in a fixed horizontal window leaves a logarithmic
derivative whose size and derivative are `O(log X)`. Conjugation symmetry
makes its vertical component `O(|Im z| log X)`, including at multiple zeros.
-/

open Complex Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

local notation "conj" => (starRingEnd ℂ)

private theorem heat_inner_anchor_norm {X : ℝ} {z : ℂ}
    (hr : |z.re - X| ≤ 1) (hi : |z.im| ≤ 1 / 2) :
    ‖z - ((X : ℂ) - 16 * I)‖ ≤ 67 / 4 := by
  have hr2 : (z.re - X) ^ 2 ≤ 1 := by
    have h := sq_le_sq₀ (abs_nonneg (z.re - X)) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr hr
    simpa only [sq_abs, one_pow] using h
  have hi' : |z.im + 16| ≤ 33 / 2 := by
    have h := abs_add_le z.im (16 : ℝ)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
    linarith only [h, hi]
  have hi2 : (z.im + 16) ^ 2 ≤ (33 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (z.im + 16)) (by norm_num : (0 : ℝ) ≤ 33 / 2)).mpr hi'
  have hn : ‖z - ((X : ℂ) - 16 * I)‖ ^ 2 =
      (z.re - X) ^ 2 + (z.im + 16) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, mul_re, re_ofNat, I_re, im_ofNat, I_im,
      mul_zero, sub_zero, sub_im, ofReal_im, mul_im, mul_one, add_zero]
    ring
  nlinarith only [hn, hr2, hi2, norm_nonneg (z - ((X : ℂ) - 16 * I))]

private theorem heat_packet_anchor_norm {X : ℝ} {z : ℂ}
    (hr : |z.re - X| ≤ 2) (hi : |z.im| ≤ 1 / 2) :
    ‖z - ((X : ℂ) - 16 * I)‖ ≤ 18 := by
  have hr2 : (z.re - X) ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg (z.re - X)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hr
    norm_num only [sq_abs, OfNat.ofNat] at h ⊢
    exact h
  have hi' : |z.im + 16| ≤ 33 / 2 := by
    have h := abs_add_le z.im (16 : ℝ)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
    linarith only [h, hi]
  have hi2 : (z.im + 16) ^ 2 ≤ (33 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (z.im + 16)) (by norm_num : (0 : ℝ) ≤ 33 / 2)).mpr hi'
  have hn : ‖z - ((X : ℂ) - 16 * I)‖ ^ 2 =
      (z.re - X) ^ 2 + (z.im + 16) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, mul_re, re_ofNat, I_re, im_ofNat, I_im,
      mul_zero, sub_zero, sub_im, ofReal_im, mul_im, mul_one, add_zero]
    ring
  nlinarith only [hn, hr2, hi2, norm_nonneg (z - ((X : ℂ) - 16 * I))]

/-- Translate the anchored factorization and identify every positive exponent
with the multiplicity of the actual heat zero. -/
private theorem heat_cofactor_actual_factors {t : ℝ} {c : ℂ} {K : ℝ}
    {T₀ : Finset ℂ} {m₀ : ℂ → ℕ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g univ) (hT : ∀ a ∈ T₀, ‖a‖ ≤ 18)
    (hgfree : ∀ w : ℂ, ‖w‖ ≤ 18 → g w ≠ 0)
    (hfac₀ : ∀ w, riemannHeat t (c + w) = (∏ a ∈ T₀, (w - a) ^ m₀ a) * g w)
    (hcount₀ : ((∑ a ∈ T₀, m₀ a : ℕ) : ℝ) ≤ K)
    (hgq : ∀ w : ℂ, ‖w‖ ≤ 17 → ‖logDeriv g w‖ ≤ K)
    (hgq' : ∀ w : ℂ, ‖w‖ ≤ 67 / 4 → ‖deriv (logDeriv g) w‖ ≤ K) :
    ∃ (A : Finset ℂ) (G : ℂ → ℂ),
      AnalyticOnNhd ℂ G univ ∧
      (∀ a ∈ A, riemannHeat t a = 0 ∧ ‖a - c‖ ≤ 18) ∧
      (∀ z : ℂ, ‖z - c‖ ≤ 18 → G z ≠ 0) ∧
      (∀ z, riemannHeat t z = (∏ a ∈ A, (z - a) ^ zeroMult (riemannHeat t) a) * G z) ∧
      ((∑ a ∈ A, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ K ∧
      (∀ z : ℂ, ‖z - c‖ ≤ 17 → ‖logDeriv G z‖ ≤ K) ∧
      (∀ z : ℂ, ‖z - c‖ ≤ 67 / 4 → ‖deriv (logDeriv G) z‖ ≤ K) := by
  classical
  let T := T₀.filter (fun a => 0 < m₀ a)
  let A := T.image (fun a => c + a)
  let m : ℂ → ℕ := fun a => m₀ (a - c)
  let G : ℂ → ℂ := fun z => g (z - c)
  have hprod (w : ℂ) : (∏ a ∈ T, (w - a) ^ m₀ a) = ∏ a ∈ T₀, (w - a) ^ m₀ a := by
    dsimp [T]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · have hm : m₀ a = 0 := by omega
      simp only [hm, pow_zero]
  have hsum : (∑ a ∈ T, m₀ a) = ∑ a ∈ T₀, m₀ a := by
    dsimp [T]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · omega
  have hinj : Set.InjOn (fun a : ℂ => c + a) T :=
    fun a _ b _ hab => add_left_cancel hab
  have hG : AnalyticOnNhd ℂ G univ := by
    intro z _
    exact (hg (z - c) (mem_univ _)).comp (f := fun w : ℂ => w - c) (x := z)
      (analyticAt_id.sub analyticAt_const)
  have hGdiff : Differentiable ℂ G := fun z => (hG z (mem_univ _)).differentiableAt
  have hGfree : ∀ z : ℂ, ‖z - c‖ ≤ 18 → G z ≠ 0 := fun z hz => hgfree _ hz
  have hfac (z : ℂ) : riemannHeat t z = (∏ a ∈ A, (z - a) ^ m a) * G z := by
    have h := hfac₀ (z - c)
    rw [add_sub_cancel, ← hprod] at h
    rw [h]
    congr 1
    rw [Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [m, add_sub_cancel_left]
    congr 1
    ring
  have hA : ∀ a ∈ A, riemannHeat t a = 0 ∧ ‖a - c‖ ≤ 18 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hb0 := Finset.mem_filter.mp hb
    have hma : m (c + b) ≠ 0 := by simpa only [m, add_sub_cancel_left] using hb0.2.ne'
    refine ⟨?_, by simpa only [add_sub_cancel_left] using hT b hb0.1⟩
    rw [hfac]
    have hp : (∏ a ∈ A, (c + b - a) ^ m a) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      rw [sub_self, zero_pow hma]
    rw [hp, zero_mul]
  have hmult : ∀ a ∈ A, zeroMult (riemannHeat t) a = m a := by
    intro a ha
    have hV : IsOpen {z : ℂ | G z ≠ 0} := isOpen_ne.preimage hGdiff.continuous
    have h := zeroMult_of_factorization hV A m hGdiff.differentiableOn
      (fun z hz => hz) (fun z _ => hfac z) (hGfree a (hA a ha).2)
    simpa only [if_pos ha] using h
  have hderivG (z : ℂ) : deriv G z = deriv g (z - c) := by
    have h := ((hg (z - c) (mem_univ _)).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).sub_const c)
    simpa only [G, Function.comp_def, id_eq, mul_one] using h.deriv
  have hqeq : logDeriv G = fun z => logDeriv g (z - c) := by
    funext z
    rw [logDeriv_apply, logDeriv_apply, hderivG]
  refine ⟨A, G, hG, hA, hGfree, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [hfac]
    congr 1
    exact Finset.prod_congr rfl fun a ha => by rw [hmult a ha]
  · have heq : (∑ a ∈ A, zeroMult (riemannHeat t) a) = ∑ a ∈ T₀, m₀ a := by
      calc
        _ = ∑ a ∈ A, m a := Finset.sum_congr rfl hmult
        _ = ∑ a ∈ T, m₀ a := by
          rw [Finset.sum_image hinj]
          simp only [m, add_sub_cancel_left]
        _ = _ := hsum
    simpa only [heq] using hcount₀
  · intro z hz
    rw [hqeq]
    exact hgq _ hz
  · intro z hz
    have hqdiff : DifferentiableAt ℂ (logDeriv g) (z - c) := by
      change DifferentiableAt ℂ (fun w => deriv g w / g w) (z - c)
      exact ((hg _ (mem_univ _)).deriv.div (hg _ (mem_univ _))
        (hgfree _ (by linarith only [hz]))).differentiableAt
    have hd := hqdiff.hasDerivAt.comp z ((hasDerivAt_id z).sub_const c)
    rw [hqeq]
    rw [show deriv (fun z => logDeriv g (z - c)) z = deriv (logDeriv g) (z - c) by
      simpa only [Function.comp_def, id_eq, mul_one] using hd.deriv]
    exact hgq' _ hz

private theorem heat_exterior_pole_distance {X : ℝ} {z a : ℂ}
    (hz : |z.re - X| ≤ 1) (ha : ¬ |a.re - X| ≤ 2) : 1 ≤ ‖z - a‖ := by
  have htri := abs_add_le (a.re - z.re) (z.re - X)
  rw [sub_add_sub_cancel, abs_sub_comm a.re z.re] at htri
  have hr := Complex.abs_re_le_norm (z - a)
  rw [Complex.sub_re] at hr
  have ha' : 2 < |a.re - X| := lt_of_not_ge ha
  linarith only [htri, hr, ha', hz]

private theorem pole_sum_hasDerivAt {B : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hne : ∀ a ∈ B, z - a ≠ 0) :
    HasDerivAt (fun w => ∑ a ∈ B, (m a : ℂ) / (w - a))
      (∑ a ∈ B, -(m a : ℂ) / (z - a) ^ 2) z := by
  apply HasDerivAt.fun_sum
  intro a ha
  simpa only [Pi.div_def, id_eq, zero_mul, mul_one, zero_sub] using
    (hasDerivAt_const z (m a : ℂ)).div ((hasDerivAt_id z).sub_const a) (hne a ha)

private theorem pole_sum_deriv_norm_le {B : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hfar : ∀ a ∈ B, 1 ≤ ‖z - a‖) :
    ‖deriv (fun w => ∑ a ∈ B, (m a : ℂ) / (w - a)) z‖ ≤ ∑ a ∈ B, (m a : ℝ) := by
  have hne : ∀ a ∈ B, z - a ≠ 0 := by
    intro a ha h
    have hbound := hfar a ha
    rw [h, norm_zero] at hbound
    norm_num at hbound
  rw [(pole_sum_hasDerivAt hne).deriv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow]
  apply div_le_self (Nat.cast_nonneg _)
  nlinarith only [hfar a ha]

private theorem norm_conj_average_le {a b : ℂ} {K : ℝ}
    (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) : ‖(a + conj b) / 2‖ ≤ K := by
  have h := (norm_add_le a (conj b)).trans (add_le_add ha (by simpa using hb))
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [h])

private theorem heat_logDeriv_conj_conj {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    conj (logDeriv (riemannHeat t) (conj z)) = logDeriv (riemannHeat t) z := by
  have hfun : (fun w => conj (riemannHeat t (conj w))) = riemannHeat t :=
    funext fun w => by rw [riemannHeat_conj ht, Complex.conj_conj]
  have hd := ((differentiable_riemannHeat ht) (conj z)).hasDerivAt.conj_conj
  change HasDerivAt (fun w => conj (riemannHeat t (conj w)))
    (conj (deriv (riemannHeat t) (conj z))) (conj (conj z)) at hd
  rw [hfun, Complex.conj_conj] at hd
  rw [logDeriv_apply, map_div₀, ← hd.deriv, riemannHeat_conj ht, Complex.conj_conj,
    logDeriv_apply]

/-- A real-on-real field with bounded derivative has vertical component
bounded by the distance to the real axis. -/
private theorem im_le_height_mul_of_deriv_bound {Q : ℂ → ℂ} {X K : ℝ}
    (hQ : ∀ z : ℂ, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      DifferentiableAt ℂ Q z ∧ ‖deriv Q z‖ ≤ K)
    (hreal : ∀ x : ℝ, (Q x).im = 0) {z : ℂ}
    (hr : |z.re - X| ≤ 1) (hi : |z.im| ≤ 1 / 2) :
    |(Q z).im| ≤ K * |z.im| := by
  let v : ℝ → ℂ := fun y => Q ((z.re : ℂ) + (y : ℂ) * I)
  have hv (y : ℝ) (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      HasDerivAt v (deriv Q ((z.re : ℂ) + (y : ℂ) * I) * I) y := by
    have hy' : |y| ≤ 1 / 2 := abs_le.mpr hy
    have hpoint := hQ ((z.re : ℂ) + (y : ℂ) * I)
      (by simpa using hr) (by simpa using hy')
    have h := hpoint.1.hasDerivAt.comp (y : ℂ)
      (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (z.re : ℂ))
    simpa only [v, Function.comp_def, id_eq, one_mul] using h.comp_ofReal
  have hbound (y : ℝ) (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : ‖deriv v y‖ ≤ K := by
    rw [(hv y hy).deriv, norm_mul, norm_I, mul_one]
    exact (hQ _ (by simpa using hr) (by simpa using (abs_le.mpr hy))).2
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hv y hy).differentiableAt) hbound (convex_Icc _ _)
    (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (abs_le.mp hi)
  have hvz : v z.im = Q z := by simp only [v, re_add_im]
  have hv0 : v 0 = Q (z.re : ℂ) := by simp only [v, ofReal_zero, zero_mul, add_zero]
  rw [hvz, hv0, sub_zero, Real.norm_eq_abs] at hmv
  have him := Complex.abs_im_le_norm (Q z - Q (z.re : ℂ))
  rw [sub_im, hreal, sub_zero] at him
  exact him.trans hmv

/-- All heat zeros in the horizontal window of radius two form a packet
of degree `O(log X)`. On the inner window its exterior logarithmic field
and derivative are `O(log X)`, and its vertical component is
`O(|Im z| log X)`. The constants are uniform down to time zero. -/
theorem exists_uniform_riemannHeat_exterior_force :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ∃ (S : Finset ℂ) (Q : ℂ → ℂ),
          (∀ a : ℂ, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2) ∧
          ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ C * Real.log X ∧
          (∀ x : ℝ, (Q x).im = 0) ∧
          ∀ z : ℂ, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
            AnalyticAt ℂ Q z ∧ ‖Q z‖ ≤ C * Real.log X ∧
            ‖deriv Q z‖ ≤ C * Real.log X ∧
            |(Q z).im| ≤ C * Real.log X * |z.im| ∧
            (riemannHeat t z ≠ 0 → logDeriv (riemannHeat t) z =
              (∑ a ∈ S, (zeroMult (riemannHeat t) a : ℂ) / (z - a)) + Q z) := by
  classical
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_local_cofactor
  refine ⟨2 * C, by positivity, X₀, hX₀, ?_⟩
  intro X hX t ht ht8 htL
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  have hCL : 0 < C * Real.log X := mul_pos hC hL
  let c : ℂ := (X : ℂ) - 16 * I
  obtain ⟨T₀, m₀, g, hg, hT, hgfree, hfac₀, hcount₀, hgq, hgq', _, _⟩ :=
    hcofactor X hX t ht ht8 htL
  obtain ⟨A, G, hG, hA, hGfree, hfac, hcount, hGq, hGq'⟩ :=
    heat_cofactor_actual_factors (c := c) hg hT hgfree hfac₀ hcount₀ hgq hgq'
  let m : ℂ → ℕ := zeroMult (riemannHeat t)
  let S := A.filter (fun a => |a.re - X| ≤ 2)
  let B := A.filter (fun a => ¬ |a.re - X| ≤ 2)
  let p : ℂ → ℂ := fun z => ∑ a ∈ S, (m a : ℂ) / (z - a)
  let b : ℂ → ℂ := fun z => ∑ a ∈ B, (m a : ℂ) / (z - a)
  let q : ℂ → ℂ := fun z => logDeriv G z + b z
  let Q : ℂ → ℂ := fun z => (q z + conj (q (conj z))) / 2
  have hGdiff : Differentiable ℂ G := fun z => (hG z (mem_univ _)).differentiableAt
  have hSmem (z : ℂ) : z ∈ S ↔ riemannHeat t z = 0 ∧ |z.re - X| ≤ 2 := by
    constructor
    · intro hz
      have h := Finset.mem_filter.mp hz
      exact ⟨(hA z h.1).1, h.2⟩
    · rintro ⟨hz, hr⟩
      refine Finset.mem_filter.mpr ⟨?_, hr⟩
      have hGz := hGfree z (heat_packet_anchor_norm hr
        (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht hz))
      by_contra hn
      have hp : (∏ a ∈ A, (z - a) ^ zeroMult (riemannHeat t) a) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun a ha => pow_ne_zero _ (sub_ne_zero.mpr ?_)
        intro heq
        exact hn (heq ▸ ha)
      exact (mul_ne_zero hp hGz) ((hfac z).symm.trans hz)
  have hSconj : ∀ a ∈ S, conj a ∈ S := by
    intro a ha
    obtain ⟨hz, hr⟩ := (hSmem a).mp ha
    apply (hSmem (conj a)).mpr
    refine ⟨?_, by simpa only [conj_re] using hr⟩
    rw [riemannHeat_conj ht, hz, map_zero]
  have hpconj (z : ℂ) : conj (p (conj z)) = p z := by
    dsimp [p]
    rw [map_sum]
    refine Finset.sum_bij (fun a _ => conj a) hSconj ?_ ?_ ?_
    · intro a _ a' _ h
      have h' := congrArg conj h
      simpa only [conj_conj] using h'
    · intro a ha
      exact ⟨conj a, hSconj a ha, conj_conj a⟩
    · intro a _
      simp only [map_div₀, map_natCast, map_sub, conj_conj, m,
        zeroMult_riemannHeat_conj ht]
  have hsmall (D : Finset ℂ) (hD : D ⊆ A) : (∑ a ∈ D, (m a : ℝ)) ≤ C * Real.log X := by
    have h := Finset.sum_le_sum_of_subset (f := m) hD
    have h' : ((∑ a ∈ D, m a : ℕ) : ℝ) ≤ ((∑ a ∈ A, m a : ℕ) : ℝ) := Nat.cast_le.mpr h
    simpa only [Nat.cast_sum] using h'.trans hcount
  have hfar (z : ℂ) (hr : |z.re - X| ≤ 1) : ∀ a ∈ B, 1 ≤ ‖z - a‖ := by
    intro a ha
    exact heat_exterior_pole_distance hr (Finset.mem_filter.mp ha).2
  have hq (z : ℂ) (hr : |z.re - X| ≤ 1) (hi : |z.im| ≤ 1 / 2) :
      AnalyticAt ℂ q z ∧ ‖q z‖ ≤ 2 * C * Real.log X ∧
      ‖deriv q z‖ ≤ 2 * C * Real.log X := by
    have hzrad : ‖z - c‖ ≤ 67 / 4 := heat_inner_anchor_norm hr hi
    have hz17 : ‖z - c‖ ≤ 17 := by linarith only [hzrad]
    have hz18 : ‖z - c‖ ≤ 18 := by linarith only [hzrad]
    have hne : ∀ a ∈ B, z - a ≠ 0 := by
      intro a ha heq
      have h := hfar z hr a ha
      rw [heq, norm_zero] at h
      norm_num at h
    have hgan : AnalyticAt ℂ (logDeriv G) z :=
      (hG z (mem_univ _)).deriv.div (hG z (mem_univ _)) (hGfree z hz18)
    have hban : AnalyticAt ℂ b z := by
      apply Finset.analyticAt_fun_sum
      intro a ha
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hne a ha)
    have hbn : ‖b z‖ ≤ C * Real.log X := by
      have h := norm_sum_multiplicity_div_le (m := m) (by norm_num : (0 : ℝ) < 1) (hfar z hr)
      rw [div_one] at h
      exact h.trans (hsmall B (Finset.filter_subset _ _))
    have hbd : ‖deriv b z‖ ≤ C * Real.log X :=
      (pole_sum_deriv_norm_le (m := m) (hfar z hr)).trans (hsmall B (Finset.filter_subset _ _))
    refine ⟨hgan.add hban, ?_, ?_⟩
    · have h := (norm_add_le (logDeriv G z) (b z)).trans (add_le_add (hGq z hz17) hbn)
      dsimp only [q]
      linarith only [h]
    · have hd : deriv q z = deriv (logDeriv G) z + deriv b z :=
        (hgan.differentiableAt.hasDerivAt.add hban.differentiableAt.hasDerivAt).deriv
      rw [hd]
      have h := (norm_add_le (deriv (logDeriv G) z) (deriv b z)).trans
        (add_le_add (hGq' z hzrad) hbd)
      linarith only [h]
  have hsplit (z : ℂ) (hr : |z.re - X| ≤ 1) (hi : |z.im| ≤ 1 / 2)
      (hz : riemannHeat t z ≠ 0) : logDeriv (riemannHeat t) z = p z + q z := by
    have hV : IsOpen {w : ℂ | G w ≠ 0} := isOpen_ne.preimage hGdiff.continuous
    have hne : ∀ a ∈ A, z ≠ a := by
      intro a ha heq
      exact hz (heq ▸ (hA a ha).1)
    have hzG : G z ≠ 0 := hGfree z
      (by have h := heat_inner_anchor_norm hr hi; exact h.trans (by norm_num))
    have h := logDeriv_of_factor hV hGdiff.differentiableOn (fun w hw => hw)
      (fun w _ => hfac w) hzG hne
    have heq : (∑ a ∈ A, (m a : ℂ) / (z - a)) = p z + b z :=
      (Finset.sum_filter_add_sum_filter_not A (fun a => |a.re - X| ≤ 2)
        (fun a => (m a : ℂ) / (z - a))).symm
    change logDeriv (riemannHeat t) z = (∑ a ∈ A, (m a : ℂ) / (z - a)) + logDeriv G z at h
    rw [heq] at h
    dsimp only [q]
    linear_combination h
  have hQreal (x : ℝ) : (Q x).im = 0 := by
    simp only [Q, conj_ofReal, div_ofNat_im, add_im, conj_im, add_neg_cancel, zero_div]
  have hQ (z : ℂ) (hr : |z.re - X| ≤ 1) (hi : |z.im| ≤ 1 / 2) :
      AnalyticAt ℂ Q z ∧ ‖Q z‖ ≤ 2 * C * Real.log X ∧
      ‖deriv Q z‖ ≤ 2 * C * Real.log X := by
    have hz := hq z hr hi
    have hc := hq (conj z) (by simpa only [conj_re] using hr)
      (by simpa only [conj_im, abs_neg] using hi)
    have hcan := RHTower.analyticAt_conj_comp_conj hc.1
    have hd := hc.1.differentiableAt.hasDerivAt.conj_conj
    rw [conj_conj] at hd
    have hdQ : HasDerivAt Q ((deriv q z + conj (deriv q (conj z))) / 2) z := by
      simpa only [Q, Function.comp_def, Pi.add_def] using
        (hz.1.differentiableAt.hasDerivAt.add hd).div_const 2
    refine ⟨(hz.1.add hcan).div analyticAt_const (by norm_num),
      norm_conj_average_le hz.2.1 hc.2.1, ?_⟩
    rw [hdQ.deriv]
    exact norm_conj_average_le hz.2.2 hc.2.2
  refine ⟨S, Q, hSmem, ?_, hQreal, ?_⟩
  · have h := hsmall S (Finset.filter_subset _ _)
    rw [Nat.cast_sum]
    dsimp only [m] at h
    linarith only [h, hCL]
  · intro z hr hi
    have hz := hQ z hr hi
    refine ⟨hz.1, hz.2.1, hz.2.2,
      im_le_height_mul_of_deriv_bound (fun w hw hiw =>
        ⟨(hQ w hw hiw).1.differentiableAt, (hQ w hw hiw).2.2⟩) hQreal hr hi, ?_⟩
    intro hHz
    have hHzc : riemannHeat t (conj z) ≠ 0 := by
      intro h
      apply hHz
      have h' := congrArg conj h
      simpa only [riemannHeat_conj ht, conj_conj, map_zero] using h'
    have hc := congrArg conj (hsplit (conj z)
      (by simpa only [conj_re] using hr) (by simpa only [conj_im, abs_neg] using hi) hHzc)
    rw [heat_logDeriv_conj_conj ht, map_add, hpconj] at hc
    have heq : conj (q (conj z)) = q z := add_left_cancel (hc.symm.trans (hsplit z hr hi hHz))
    have hQq : Q z = q z := by dsimp only [Q]; rw [heq]; ring
    rw [hQq]
    exact hsplit z hr hi hHz

end

end RHTower.DeBruijn
