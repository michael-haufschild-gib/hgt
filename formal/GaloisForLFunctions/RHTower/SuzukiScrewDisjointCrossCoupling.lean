import GaloisForLFunctions.RHTower.SuzukiExplicitScrewRegularKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Disjointly supported positive cross couplings of the regular screw kernel

Beyond the sign threshold `t_* = log ρ` the regular screw kernel is strictly positive.  Since the
kernel enters the restricted Weil form as `K (x - y)`, two nonnegative bumps placed at `-t/2` and
`t/2` with `t > t_*` have **positive** cross pairing even though their supports are disjoint.

That is the exact opposite of the first Beurling–Deny inequality, which any positivity preserving
semigroup would force.  Adding a scalar multiple of the `L²` pairing cannot repair it, because the
`L²` pairing of two disjointly supported functions vanishes identically.  So no scalar shift of the
form carries a positivity preserving semigroup once the aperture exceeds `t_*/2`.

The module supplies:

* `exists_atomFree_mem_Ioo` — every nonempty open interval contains a point which is not a
  prime-power atom `log n`, `n ≥ 2` (the atoms in a bounded interval form a finite set);
* `exists_atomFree_radius` — a whole interval around a non-atom avoids the atoms;
* `exists_disjoint_positive_screwRegularForm` — the construction of the two bumps and the strict
  positivity of the resulting double integral;
* `not_satisfiesBeurlingDeny_screwRegularForm_add_smul` — no scalar shift satisfies the first
  Beurling–Deny inequality.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

/-! ## Prime-power atoms -/

/-- The prime-power atoms `log n`, `n ≥ 2`, of the screw distribution. -/
def screwAtoms : Set ℝ := {x : ℝ | ∃ n : ℕ, 2 ≤ n ∧ x = Real.log n}

theorem mem_screwAtoms_iff {x : ℝ} : x ∈ screwAtoms ↔ ∃ n : ℕ, 2 ≤ n ∧ x = Real.log n := Iff.rfl

/-- The atoms below a given bound form a finite set. -/
theorem screwAtoms_inter_Iio_subset (β : ℝ) :
    screwAtoms ∩ Iio β
      ⊆ ((Finset.Icc 2 ⌊Real.exp β⌋₊).image fun n : ℕ => Real.log n : Finset ℝ) := by
  rintro x ⟨⟨n, hn, rfl⟩, hxβ⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : (n : ℝ) < Real.exp β := by
    have := hxβ
    exact (Real.log_lt_iff_lt_exp hnpos).mp this
  have hle : n ≤ ⌊Real.exp β⌋₊ := Nat.le_floor hlt.le
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc]
  exact ⟨n, ⟨hn, hle⟩, rfl⟩

/-- **Every nonempty open interval contains a non-atom.** -/
theorem exists_atomFree_mem_Ioo {α β : ℝ} (h : α < β) :
    ∃ t ∈ Ioo α β, ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n := by
  classical
  set F : Finset ℝ := (Finset.Icc 2 ⌊Real.exp β⌋₊).image fun n : ℕ => Real.log n with hF
  have hinf : (Ioo α β \ (F : Set ℝ)).Infinite :=
    (Set.Ioo_infinite h).sdiff F.finite_toSet
  obtain ⟨t, htIoo, htF⟩ := hinf.nonempty
  refine ⟨t, htIoo, fun n hn hlog => htF ?_⟩
  have hmem : t ∈ screwAtoms ∩ Iio β := ⟨⟨n, hn, hlog⟩, htIoo.2⟩
  exact screwAtoms_inter_Iio_subset β hmem

/-- **A whole interval around a non-atom avoids the atoms.** -/
theorem exists_atomFree_radius {t : ℝ} (hatom : ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → ∀ n : ℕ, 2 ≤ n → s ≠ Real.log n := by
  classical
  set F : Finset ℝ := (Finset.Icc 2 ⌊Real.exp (t + 1)⌋₊).image fun n : ℕ => Real.log n with hF
  have htF : t ∉ (F : Set ℝ) := by
    intro hmem
    simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc] at hmem
    obtain ⟨n, hn, hlog⟩ := hmem
    exact hatom n hn.1 hlog.symm
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (F.finite_toSet.isClosed.isOpen_compl) t htF
  refine ⟨min 1 ε, lt_min one_pos hε, fun s hs n hn hlog => ?_⟩
  have hs1 : |s - t| < 1 := lt_of_lt_of_le hs (min_le_left _ _)
  have hsε : |s - t| < ε := lt_of_lt_of_le hs (min_le_right _ _)
  have hsmem : s ∈ Metric.ball t ε := by
    simp only [Metric.mem_ball, Real.dist_eq]
    exact hsε
  refine (hball hsmem) ?_
  have hupper : s < t + 1 := by
    have := abs_lt.mp hs1
    linarith [this.2]
  have hmem : s ∈ screwAtoms ∩ Iio (t + 1) := ⟨⟨n, hn, hlog⟩, hupper⟩
  exact screwAtoms_inter_Iio_subset (t + 1) hmem

/-! ## The regular-kernel cross form -/

/-- The cross pairing of the regular screw kernel: the ordinary double integral
`∫∫ K (x - y) f y h x`.  On pairs of disjointly supported test functions whose support difference
avoids `0` and all prime-power atoms, this is the restricted Weil form. -/
def screwRegularForm (f h : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, screwRegularKernel (p.1 - p.2) * f p.2 * h p.1

/-- The `L²` pairing. -/
def screwL2Pairing (f h : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x * h x

/-- Two functions with disjoint supports pair to zero in `L²`. -/
theorem screwL2Pairing_eq_zero_of_disjoint {f h : ℝ → ℝ}
    (hd : Disjoint (Function.support f) (Function.support h)) : screwL2Pairing f h = 0 := by
  have hzero : (fun x : ℝ => f x * h x) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    by_cases hx : f x = 0
    · rw [hx, zero_mul]
    · have hxs : x ∈ Function.support f := hx
      have : x ∉ Function.support h := fun hxh =>
        (Set.disjoint_left.mp hd hxs) hxh
      rw [Function.notMem_support.mp this, mul_zero]
  rw [screwL2Pairing, hzero, integral_zero]

/-- The first Beurling–Deny inequality for a real bilinear pairing of functions on the line:
nonnegative vectors with disjoint supports have nonpositive cross value. -/
def SatisfiesBeurlingDeny (Q : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) : Prop :=
  ∀ f h : ℝ → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ h x) →
    Disjoint (Function.support f) (Function.support h) → Q f h ≤ 0

/-! ## Continuity of the kernel off the diagonal -/

theorem continuousOn_screwRegularKernel : ContinuousOn screwRegularKernel (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  have hden : (1 : ℝ) - Real.exp (-(2 * t)) ≠ 0 :=
    ne_of_gt (one_sub_exp_neg_two_mul_pos ht')
  have h1 : ContinuousAt (fun s : ℝ => Real.exp (s / 2)) t := by fun_prop
  have h2 : ContinuousAt (fun s : ℝ => Real.exp (-(5 * s / 2))) t := by fun_prop
  have h3 : ContinuousAt (fun s : ℝ => 1 - Real.exp (-(2 * s))) t := by fun_prop
  have hdiv : ContinuousAt
      (fun s : ℝ => Real.exp (-(5 * s / 2)) / (1 - Real.exp (-(2 * s)))) t :=
    ContinuousAt.div h2 h3 hden
  exact ((h1.sub hdiv).continuousWithinAt)

/-! ## The construction -/

/-- **Positive cross coupling at disjoint supports.**  For every aperture `a > t_*/2` there are
two nonzero nonnegative smooth compactly supported bumps inside `(-a, a)` with disjoint supports,
whose support difference stays strictly beyond the sign threshold and avoids every prime-power
atom, and whose regular screw pairing is strictly positive. -/
theorem exists_disjoint_positive_screwRegularForm {a : ℝ} (ha : screwSignThreshold / 2 < a) :
    ∃ f h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ h x) ∧
      (∃ x, f x ≠ 0) ∧ (∃ x, h x ≠ 0) ∧
      Function.support f ⊆ Ioo (-a) a ∧ Function.support h ⊆ Ioo (-a) a ∧
      Disjoint (Function.support f) (Function.support h) ∧
      HasCompactSupport f ∧ HasCompactSupport h ∧
      (∀ x ∈ tsupport h, ∀ y ∈ tsupport f,
        screwSignThreshold < x - y ∧ ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) ∧
      0 < screwRegularForm f h := by
  classical
  have hthr : 0 < screwSignThreshold := screwSignThreshold_pos
  -- an atom-free gap `t` strictly between the threshold and the aperture width
  obtain ⟨t, htIoo, hatom⟩ :=
    exists_atomFree_mem_Ioo (show screwSignThreshold < 2 * a by linarith)
  obtain ⟨htl, htr⟩ := htIoo
  have htpos : 0 < t := lt_trans hthr htl
  obtain ⟨ε, hε, hεatom⟩ := exists_atomFree_radius hatom
  -- the radius
  set r : ℝ := min (min ((t - screwSignThreshold) / 4) (ε / 4)) (min ((a - t / 2) / 2) (t / 4))
    with hrdef
  have hr1 : r ≤ (t - screwSignThreshold) / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ ε / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ (a - t / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr4 : r ≤ t / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hrpos : 0 < r := by
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  -- the two bumps
  set F : ContDiffBump (-(t / 2) : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩ with hFdef
  set H : ContDiffBump (t / 2 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩ with hHdef
  have hFout : F.rOut = r := rfl
  have hHout : H.rOut = r := rfl
  have hFsupp : Function.support (F : ℝ → ℝ) = Ioo (-(t / 2) - r) (-(t / 2) + r) := by
    rw [F.support_eq, hFout, Real.ball_eq_Ioo]
  have hHsupp : Function.support (H : ℝ → ℝ) = Ioo (t / 2 - r) (t / 2 + r) := by
    rw [H.support_eq, hHout, Real.ball_eq_Ioo]
  -- the compact rectangle carrying the integrand
  set Kx : Set ℝ := Icc (t / 2 - r) (t / 2 + r) with hKx
  set Ky : Set ℝ := Icc (-(t / 2) - r) (-(t / 2) + r) with hKy
  set R : Set (ℝ × ℝ) := Kx ×ˢ Ky with hR
  have hRcompact : IsCompact R := (isCompact_Icc).prod isCompact_Icc
  have hRmeas : MeasurableSet R := (measurableSet_Icc).prod measurableSet_Icc
  -- on the rectangle the kernel argument is a positive non-atom
  have hgap : ∀ p ∈ R, screwSignThreshold < p.1 - p.2 ∧ |p.1 - p.2 - t| < ε := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨hx1, hx2⟩ := hp1
    obtain ⟨hy1, hy2⟩ := hp2
    constructor
    · linarith
    · rw [abs_lt]; constructor <;> linarith
  have hKpos : ∀ p ∈ R, 0 < screwRegularKernel (p.1 - p.2) := by
    intro p hp
    obtain ⟨hlt, _⟩ := hgap p hp
    have hpos : 0 < p.1 - p.2 := lt_trans hthr hlt
    exact (screwRegularKernel_pos_iff hpos).mpr hlt
  -- the integrand
  set G : ℝ × ℝ → ℝ := fun p => screwRegularKernel (p.1 - p.2) * F p.2 * H p.1 with hG
  have hGnonneg : ∀ p ∈ R, 0 ≤ G p := by
    intro p hp
    exact mul_nonneg (mul_nonneg (hKpos p hp).le F.nonneg) H.nonneg
  have hGzero : ∀ p ∉ R, G p = 0 := by
    intro p hp
    by_cases hFp : (F : ℝ → ℝ) p.2 = 0
    · simp [hG, hFp]
    by_cases hHp : (H : ℝ → ℝ) p.1 = 0
    · simp [hG, hHp]
    exfalso
    have hp2 : p.2 ∈ Ioo (-(t / 2) - r) (-(t / 2) + r) := by
      rw [← hFsupp]; exact hFp
    have hp1 : p.1 ∈ Ioo (t / 2 - r) (t / 2 + r) := by
      rw [← hHsupp]; exact hHp
    exact hp (Set.mem_prod.mpr ⟨⟨hp1.1.le, hp1.2.le⟩, ⟨hp2.1.le, hp2.2.le⟩⟩)
  have hGcont : ContinuousOn G R := by
    have hker : ContinuousOn (fun p : ℝ × ℝ => screwRegularKernel (p.1 - p.2)) R := by
      refine ContinuousOn.comp continuousOn_screwRegularKernel ?_ ?_
      · exact (continuous_fst.sub continuous_snd).continuousOn
      · intro p hp
        obtain ⟨hlt, _⟩ := hgap p hp
        exact lt_trans hthr hlt
    exact (hker.mul ((F.continuous.comp continuous_snd).continuousOn)).mul
      ((H.continuous.comp continuous_fst).continuousOn)
  have hGint : IntegrableOn G R volume := hGcont.integrableOn_compact hRcompact
  -- the open rectangle sits inside the support
  have hOsub : Ioo (t / 2 - r) (t / 2 + r) ×ˢ Ioo (-(t / 2) - r) (-(t / 2) + r)
      ⊆ Function.support G ∩ R := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    have hpR : p ∈ R := Set.mem_prod.mpr ⟨⟨hp1.1.le, hp1.2.le⟩, ⟨hp2.1.le, hp2.2.le⟩⟩
    refine ⟨?_, hpR⟩
    have h1 : (F : ℝ → ℝ) p.2 ≠ 0 := by rw [← Function.mem_support, hFsupp]; exact hp2
    have h2 : (H : ℝ → ℝ) p.1 ≠ 0 := by rw [← Function.mem_support, hHsupp]; exact hp1
    have h3 : screwRegularKernel (p.1 - p.2) ≠ 0 := ne_of_gt (hKpos p hpR)
    simpa [hG] using mul_ne_zero (mul_ne_zero h3 h1) h2
  have hvolO : 0 < volume (Function.support G ∩ R) := by
    refine lt_of_lt_of_le ?_ (measure_mono hOsub)
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    have h2r : (0 : ℝ) < 2 * r := by linarith
    have e1 : t / 2 + r - (t / 2 - r) = 2 * r := by ring
    have e2 : -(t / 2) + r - (-(t / 2) - r) = 2 * r := by ring
    rw [e1, e2]
    exact ENNReal.mul_pos (by simpa using hrpos) (by simpa using hrpos)
  have hae : 0 ≤ᵐ[volume.restrict R] G := by
    filter_upwards [ae_restrict_mem hRmeas] with p hp
    exact hGnonneg p hp
  have hpos : 0 < ∫ p in R, G p := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hae hGint]
    exact hvolO
  have hform : screwRegularForm (F : ℝ → ℝ) (H : ℝ → ℝ) = ∫ p in R, G p := by
    rw [screwRegularForm, ← setIntegral_eq_integral_of_forall_compl_eq_zero hGzero]
  refine ⟨(F : ℝ → ℝ), (H : ℝ → ℝ), F.contDiff, H.contDiff, fun _ => F.nonneg,
    fun _ => H.nonneg, ⟨-(t / 2), ?_⟩, ⟨t / 2, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ne_of_gt (F.pos_of_mem_ball (by simpa [hFout] using hrpos))
  · exact ne_of_gt (H.pos_of_mem_ball (by simpa [hHout] using hrpos))
  · rw [hFsupp]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [hHsupp]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [hFsupp, hHsupp, Set.disjoint_left]
    intro x hx hx'
    have := hx.2
    have := hx'.1
    linarith
  · exact F.hasCompactSupport
  · exact H.hasCompactSupport
  · intro x hx y hy
    rw [H.tsupport_eq, hHout, Real.closedBall_eq_Icc] at hx
    rw [F.tsupport_eq, hFout, Real.closedBall_eq_Icc] at hy
    have hpR : ((x, y) : ℝ × ℝ) ∈ R := by
      refine Set.mem_prod.mpr ⟨?_, ?_⟩
      · rw [hKx]; exact hx
      · rw [hKy]; exact hy
    obtain ⟨hlt, habs⟩ := hgap (x, y) hpR
    exact ⟨hlt, fun n hn => hεatom (x - y) habs n hn⟩
  · rw [hform]; exact hpos

/-- **No scalar shift of the restricted regular screw form satisfies the first Beurling–Deny
inequality once the aperture exceeds `t_*/2`.**  Hence no such shift generates a positivity
preserving — a fortiori positivity improving — semigroup. -/
theorem not_satisfiesBeurlingDeny_screwRegularForm_add_smul (c : ℝ) {a : ℝ}
    (ha : screwSignThreshold / 2 < a) :
    ¬ SatisfiesBeurlingDeny fun f h => screwRegularForm f h + c * screwL2Pairing f h := by
  intro hBD
  obtain ⟨f, h, _, _, hfnn, hhnn, _, _, _, _, hdisj, _, _, _, hposform⟩ :=
    exists_disjoint_positive_screwRegularForm ha
  have hle := hBD f h hfnn hhnn hdisj
  simp only [screwL2Pairing_eq_zero_of_disjoint hdisj, mul_zero, add_zero] at hle
  linarith

end GaloisForLFunctions.RHTower

end
