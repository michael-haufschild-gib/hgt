import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.JointEulerFactorization

/-!
# Interior persistence of poles along bounded analytic gauge paths

A normal prime bound on one parameter disk propagates to every compact
subdisk. Weighted square-root estimates preserve a positive saving.
At real parameters, unit prime phases then give nonzero pole residues
and actual joint regularizations.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- A small centered disk controls any compact subdisk by a fixed dyadic power. -/
theorem exists_compact_disk_power_bound {r₀ r R M : ℝ}
    (hr₀ : 0 < r₀) (hr : 0 < r) (hrR : r < R) (hM : 0 < M) :
    ∃ N : ℕ, ∀ (f : ℂ → ℂ) (m : ℝ), 0 < m →
      DifferentiableOn ℂ f (ball 0 R) →
      (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) →
      (∀ z : ℂ, ‖z‖ ≤ r₀ → ‖f z‖ ≤ m) →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ M * (m / M) ^ ((1 / 2 : ℝ) ^ N) := by
  let ρ := min r₀ ((R - r) / 8)
  have hρ : 0 < ρ := lt_min hr₀ (by positivity)
  have hρ₀ : ρ ≤ r₀ := min_le_left _ _
  have hρR : ρ ≤ (R - r) / 8 := min_le_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (r / ρ)
  have hNp : 0 < (N : ℝ) := (div_pos hr hρ).trans hN
  have hNne : (N : ℝ) ≠ 0 := hNp.ne'
  have hstepbound : r / (N : ℝ) ≤ ρ := by
    apply (div_le_iff₀ hNp).mpr
    exact ((div_lt_iff₀ hρ).mp hN).le.trans_eq (mul_comm _ _)
  refine ⟨N, ?_⟩
  intro f m hm hd hb hs z hz
  by_cases hmM : m ≤ M
  · let q : ℕ → ℂ := fun k => (((k : ℝ) / (N : ℝ) : ℝ) : ℂ) * z
    have hq0 : q 0 = 0 := by simp [q]
    have hqN : q N = z := by
      change (((N : ℝ) / (N : ℝ) : ℝ) : ℂ) * z = z
      rw [div_self hNne, ofReal_one, one_mul]
    have hqbound (k : ℕ) (hk : k ≤ N) : ‖q k‖ ≤ r := by
      have hfrac : 0 ≤ (k : ℝ) / (N : ℝ) := by positivity
      have hfrac1 : (k : ℝ) / (N : ℝ) ≤ 1 :=
        (div_le_one hNp).mpr (by exact_mod_cast hk)
      simp only [q, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hfrac]
      exact (mul_le_mul_of_nonneg_right hfrac1 (norm_nonneg z)).trans (by simpa using hz)
    have hstep (k : ℕ) : ‖q (k + 1) - q k‖ ≤ ρ := by
      rw [show q (k + 1) - q k = z / (N : ℂ) by
        dsimp [q]; push_cast; ring]
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right hz hNp.le).trans hstepbound
    have hinside (k : ℕ) (hk : k ≤ N) (w : ℂ) (hw : ‖w - q k‖ ≤ 4 * ρ) :
        w ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      have hn : ‖w‖ ≤ ‖w - q k‖ + ‖q k‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - q k) (q k)
      have hq := hqbound k hk
      linarith only [hn, hw, hq, hρR, hrR]
    have ha : 0 < m / M := div_pos hm hM
    have ha1 : m / M ≤ 1 := (div_le_one hM).mpr hmM
    have hsmall (w : ℂ) (hw : ‖w - q 0‖ ≤ ρ) : ‖f w‖ ≤ (m / M) * M := by
      rw [hq0, sub_zero] at hw
      rw [div_mul_cancel₀ _ hM.ne']
      exact hs w (hw.trans hρ₀)
    have hh := GaloisForLFunctions.ArithmeticAuxiliaryDynamics.norm_le_of_chain
      hρ ha ha1 hM hstep
      (fun k hk w hw => hd.differentiableAt (isOpen_ball.mem_nhds (hinside k hk w hw)))
      (fun k hk w hw => hb w (hinside k hk w hw)) hsmall N le_rfl z
      (by rw [hqN, sub_self, norm_zero]; exact hρ.le)
    exact hh.trans_eq (mul_comm _ _)
  · have hratio : 1 ≤ m / M := (one_le_div hM).mpr (le_of_not_ge hmM)
    have hp : 1 ≤ (m / M) ^ ((1 / 2 : ℝ) ^ N) :=
      Real.one_le_rpow hratio (by positivity)
    have hbound := hb z (by simpa only [mem_ball, dist_zero_right] using hz.trans_lt hrR)
    exact hbound.trans (by nlinarith only [hp, hM])

/-- Normal prime summability on one disk propagates to every compact subdisk. -/
theorem normal_summability_on_compact_disk {u : Nat.Primes → ℂ → ℂ} {R M r₀ σ₀ r : ℝ}
    (hr₀ : 0 < r₀) (hr₀R : r₀ < R) (hσ₀ : 1 / 2 < σ₀) (hσ₁ : σ₀ < 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hs : Summable (fun p => primeDiskDeviation u r₀ p * (p : ℝ) ^ (-σ₀)))
    (hr : 0 < r) (hrR : r < R) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p => primeDiskDeviation u r p * (p : ℝ) ^ (-σ)) := by
  let B := |M| + 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hfb (p : Nat.Primes) (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : ‖u p z - 1‖ ≤ B := by
    have hn := norm_sub_le (u p z) (1 : ℂ)
    rw [norm_one] at hn
    dsimp only [B]
    linarith only [hn, hb p z hz, le_abs_self M]
  let A : Nat.Primes → ℝ := fun p => primeDiskDeviation u r₀ p + (p : ℝ) ^ (-2 : ℝ)
  have hA (p : Nat.Primes) : 0 < A p := add_pos_of_nonneg_of_pos
    (primeDiskDeviation_bounds hr₀.le hr₀R hb p).1
    (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _)
  have hAs : Summable (fun p => A p * (p : ℝ) ^ (-σ₀)) := by
    have hh := summable_primeDamping (show 1 < 2 + σ₀ by linarith only [hσ₀])
    change Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 + σ₀))) at hh
    have he (p : Nat.Primes) : A p * (p : ℝ) ^ (-σ₀) =
        primeDiskDeviation u r₀ p * (p : ℝ) ^ (-σ₀) + (p : ℝ) ^ (-(2 + σ₀)) := by
      dsimp only [A]
      rw [add_mul, ← Real.rpow_add (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ))]
      congr 2
      ring
    simpa only [he] using hs.add hh
  obtain ⟨N, hprop⟩ := exists_compact_disk_power_bound hr₀ hr hrR hB
  let a : Nat.Primes → ℝ := fun p => A p / B
  have ha (p : Nat.Primes) : 0 ≤ a p := (div_pos (hA p) hB).le
  have has : Summable (fun p => a p * (p : ℝ) ^ (-σ₀)) := by
    simpa only [a, div_mul_eq_mul_div] using hAs.div_const B
  let δ := 1 - σ₀
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hσ₁]
  have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith only [hσ₀]
  let d := δ / (4 : ℝ) ^ N
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdle : d ≤ δ := div_le_self hδ.le (one_le_pow₀ (by norm_num))
  have hsA := summable_prime_dyadic_rpow ha hδ
    (show Summable (fun p => a p * (p : ℝ) ^ (-(1 - δ))) by
      simpa only [δ, sub_sub_cancel] using has) N
  have hmajor : Summable (fun p => (B * a p ^ ((1 / 2 : ℝ) ^ N)) *
      (p : ℝ) ^ (-(1 - d))) := by
    simpa only [d, mul_assoc] using hsA.mul_left B
  have hsup (p : Nat.Primes) : primeDiskDeviation u r p ≤ B * a p ^ ((1 / 2 : ℝ) ^ N) := by
    apply csSup_le
    · exact ⟨_, ⟨0, mem_closedBall_self hr.le, rfl⟩⟩
    rintro v ⟨z, hz, rfl⟩
    apply hprop (fun w => u p w - 1) (A p) (hA p) ((hu p).sub_const 1) (hfb p)
    · intro w hw
      exact ((primeDiskDeviation_bounds hr₀.le hr₀R hb p).2 w hw).trans
        (le_add_of_nonneg_right (by positivity))
    · simpa only [mem_closedBall, dist_zero_right] using hz
  refine ⟨1 - d, by linarith only [hdle, hδhalf], by linarith only [hdpos], ?_⟩
  apply hmajor.of_nonneg_of_le
    (fun p => mul_nonneg (primeDiskDeviation_bounds hr.le hrR hb p).1 (by positivity))
  exact fun p => mul_le_mul_of_nonneg_right (hsup p) (by positivity)

/-- A single actual joint pole germ controls every compact complex parameter disk. -/
theorem joint_pole_compact_normal_summability {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hgerm : ∃ (ε : ℝ) (U : ℂ × ℂ → ℂ), 0 < ε ∧ ε < R ∧ AnalyticAt ℂ U (0, 1) ∧
      ∀ t : ℝ, |t| < ε → ∀ s ∈ ball (1 : ℂ) ε, 1 < s.re →
        U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p => primeDiskDeviation u r p * (p : ℝ) ^ (-σ)) := by
  obtain ⟨r₀, σ₀, hr₀, hr₀R, hσ₀, hσ₁, hs⟩ :=
    (joint_pole_regularization_iff_normal_summability hR hu0 hu hb hphase).mp hgerm
  exact normal_summability_on_compact_disk hr₀ hr₀R hσ₀ hσ₁ hu hb hs hr hrR

/-- Normal summability gives the actual joint regularization at every real interior parameter. -/
theorem joint_regularization_at_real_of_compact_normal {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {R M t r σ : ℝ}
    (ht : |t| < r) (hrR : r < R) (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ a : ℝ, |a| < R → ∀ p, u p (a : ℂ) = twist (x a) p)
    (hs : Summable (fun p => primeDiskDeviation u r p * (p : ℝ) ^ (-σ))) :
    AnalyticAt ℂ (jointGaugeRegularization u) ((t : ℂ), 1) ∧
      jointGaugeRegularization u ((t : ℂ), 1) ≠ 0 ∧
      ∀ a : ℝ, |a| < R → ∀ s : ℂ, 1 < s.re →
        jointGaugeRegularization u ((a : ℂ), s) = (s - 1) * gaugeFibre (x a) s := by
  let S := r - |t|
  have hS : 0 < S := by dsimp [S]; linarith only [ht]
  have hr : 0 < r := (abs_nonneg t).trans_lt ht
  let v : Nat.Primes → ℂ → ℂ := fun p z => u p (z + (t : ℂ))
  have hmap (z : ℂ) (hz : ‖z‖ < S) : ‖z + (t : ℂ)‖ < r := by
    have hn := norm_add_le z (t : ℂ)
    rw [norm_real, Real.norm_eq_abs] at hn
    dsimp only [S] at hz
    linarith only [hn, hz]
  have hinside (z : ℂ) (hz : z ∈ ball (0 : ℂ) S) : z + (t : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right] at hz ⊢
    exact (hmap z hz).trans hrR
  have hv (p : Nat.Primes) : DifferentiableOn ℂ (v p) (ball 0 S) := by
    intro z hz
    exact (((hu p).differentiableAt (isOpen_ball.mem_nhds (hinside z hz))).comp z
      (differentiableAt_id.add_const (t : ℂ))).differentiableWithinAt
  have hvb (p : Nat.Primes) (z : ℂ) (hz : z ∈ ball (0 : ℂ) S) : ‖v p z‖ ≤ M :=
    hb p _ (hinside z hz)
  have hv0 (p : Nat.Primes) : ‖v p 0‖ ≤ 1 := by
    dsimp only [v]
    rw [zero_add, hphase t (ht.trans hrR), norm_twist_prime (x t) p p.2]
  have hSr : 0 < S / 2 := by positivity
  have hSrS : S / 2 < S := by linarith only [hS]
  have hsup (p : Nat.Primes) : primeDiskDeviation v (S / 2) p ≤ primeDiskDeviation u r p := by
    apply csSup_le
    · exact ⟨_, ⟨0, mem_closedBall_self hSr.le, rfl⟩⟩
    rintro b ⟨z, hz, rfl⟩
    apply (primeDiskDeviation_bounds hr.le hrR hb p).2
    apply (hmap z ?_).le
    have hz' : ‖z‖ ≤ S / 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact hz'.trans_lt hSrS
  have hvs : Summable (fun p => primeDiskDeviation v (S / 2) p * (p : ℝ) ^ (-σ)) :=
    hs.of_nonneg_of_le
      (fun p => mul_nonneg (primeDiskDeviation_bounds hSr.le hSrS hvb p).1 (by positivity))
      (fun p => mul_le_mul_of_nonneg_right (hsup p) (by positivity))
  obtain ⟨ρ, b, hρ, _, _, _, _, hW⟩ :=
    exists_jointEuler_normal_form hS hSr hSrS hσ hv hvb hv0 hvs
  have hW0 : AnalyticAt ℂ (jointGaugeRegularization v) (0, 1) :=
    hW (0, 1) ⟨by simpa only [norm_zero] using hρ, hσ1⟩
  have hWc : AnalyticAt ℂ (jointGaugeRegularization v) ((t : ℂ) - (t : ℂ), 1) := by
    simpa only [sub_self] using hW0
  have hshift : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1 - (t : ℂ), q.2)) ((t : ℂ), 1) :=
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).sub analyticAt_const).prod
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _)
  refine ⟨?_, ?_, fun a ha s hse => jointGaugeRegularization_eq_gaugeFibre (hphase a ha) hse⟩
  · have hh := hWc.comp (f := fun q : ℂ × ℂ => (q.1 - (t : ℂ), q.2)) hshift
    have heq : (fun q : ℂ × ℂ => jointGaugeRegularization v (q.1 - (t : ℂ), q.2)) =
        jointGaugeRegularization u := by
      funext q
      simp only [jointGaugeRegularization, jointDeformationExponent, jointEulerChange,
        v, sub_add_cancel]
    change AnalyticAt ℂ (fun q : ℂ × ℂ => jointGaugeRegularization v (q.1 - (t : ℂ), q.2))
      ((t : ℂ), 1) at hh
    rw [heq] at hh
    exact hh
  · change zetaResidueFactor 1 * Complex.exp (jointDeformationExponent u ((t : ℂ), 1)) ≠ 0
    rw [zetaResidueFactor_one, one_mul]
    exact Complex.exp_ne_zero _

/-- One pole germ forces nonzero joint regularizations throughout the real interior. -/
theorem joint_pole_persists_at_every_real_parameter {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hgerm : ∃ (ε : ℝ) (U : ℂ × ℂ → ℂ), 0 < ε ∧ ε < R ∧ AnalyticAt ℂ U (0, 1) ∧
      ∀ t : ℝ, |t| < ε → ∀ s ∈ ball (1 : ℂ) ε, 1 < s.re →
        U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s)
    (t : ℝ) (ht : |t| < R) :
    AnalyticAt ℂ (jointGaugeRegularization u) ((t : ℂ), 1) ∧
      jointGaugeRegularization u ((t : ℂ), 1) ≠ 0 ∧
      ∀ a : ℝ, |a| < R → ∀ s : ℂ, 1 < s.re →
        jointGaugeRegularization u ((a : ℂ), s) = (s - 1) * gaugeFibre (x a) s := by
  let r := (|t| + R) / 2
  have htr : |t| < r := by dsimp [r]; linarith only [ht]
  have hrR : r < R := by dsimp [r]; linarith only [ht]
  obtain ⟨σ, hσ, hσ1, hs⟩ := joint_pole_compact_normal_summability
    hR hu0 hu hb hphase hgerm ((abs_nonneg t).trans_lt htr) hrR
  exact joint_regularization_at_real_of_compact_normal htr hrR hσ hσ1 hu hb hphase hs

/-- A bounded analytic path with one pole germ cannot acquire a holomorphic interior fibre. -/
theorem joint_pole_excludes_holomorphic_interior_fibre {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hgerm : ∃ (ε : ℝ) (U : ℂ × ℂ → ℂ), 0 < ε ∧ ε < R ∧ AnalyticAt ℂ U (0, 1) ∧
      ∀ t : ℝ, |t| < ε → ∀ s ∈ ball (1 : ℂ) ε, 1 < s.re →
        U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s)
    (t : ℝ) (ht : |t| < R) :
    ¬ ∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre (x t) s := by
  rintro ⟨G, hG, heG⟩
  obtain ⟨hW, hWne, he⟩ := joint_pole_persists_at_every_real_parameter
    hR hu0 hu hb hphase hgerm t ht
  have hWs : AnalyticAt ℂ (fun s : ℂ => jointGaugeRegularization u ((t : ℂ), s)) 1 :=
    hW.comp (f := fun s : ℂ => ((t : ℂ), s)) (analyticAt_const.prod analyticAt_id)
  have hreg : AnalyticAt ℂ (fun s : ℂ => (s - 1) * G s) 1 :=
    (analyticAt_id.sub analyticAt_const).mul hG
  obtain ⟨ε, hε, hεG⟩ := Metric.mem_nhds_iff.mp heG
  have hFjoint : AnalyticAt ℂ (fun q : ℂ × ℂ => jointGaugeRegularization u ((t : ℂ), q.2))
      (0, 1) := hWs.comp (g := fun s : ℂ => jointGaugeRegularization u ((t : ℂ), s))
      (f := fun q : ℂ × ℂ => q.2)
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt ((0 : ℂ), (1 : ℂ)))
  have hGjoint : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.2 - 1) * G q.2) (0, 1) :=
    hreg.comp (g := fun s : ℂ => (s - 1) * G s) (f := fun q : ℂ × ℂ => q.2)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt ((0 : ℂ), (1 : ℂ)))
  have hid := joint_germ_eq_of_real_euler_agreement hε hFjoint hGjoint (by
    intro a _ s hs hse
    rw [he t ht s hse, hεG hs hse])
  have hval := hid.eq_of_nhds
  simp only [sub_self, zero_mul] at hval
  exact hWne hval

#print axioms joint_pole_compact_normal_summability
#print axioms joint_pole_persists_at_every_real_parameter
#print axioms joint_pole_excludes_holomorphic_interior_fibre

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
