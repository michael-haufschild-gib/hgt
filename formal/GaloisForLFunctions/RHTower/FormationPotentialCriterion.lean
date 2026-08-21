import GaloisForLFunctions.RHTower.RenormalizedFormationWorkDivisor
import GaloisForLFunctions.RHTower.HighExponentShellManuscriptCapstone
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.HTGeometry.HolomorphicBranch
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection

/-!
# The holomorphic formation-potential criterion

The survival transfer is zero-free on the strict right half-plane and its poles are exactly the
strict-right zeta zeros.  Consequently the Riemann hypothesis is equivalent to holomorphy of the
transfer there, to its holomorphy together with nonvanishing, and — the half-plane being convex
and hence simply connected — to global exactness of the renormalized formation work: the existence
of a holomorphic potential with `R = exp(-Φ)`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The strict right half-plane. -/
def strictRightHalfPlane : Set ℂ := {s : ℂ | 1 / 2 < s.re}

@[simp] theorem mem_strictRightHalfPlane {s : ℂ} :
    s ∈ strictRightHalfPlane ↔ 1 / 2 < s.re := Iff.rfl

theorem isOpen_strictRightHalfPlane : IsOpen strictRightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_strictRightHalfPlane : Convex ℝ strictRightHalfPlane := convex_halfSpace_re_gt _

theorem isSimplyConnected_strictRightHalfPlane : IsSimplyConnected strictRightHalfPlane :=
  GaloisForLFunctions.HTGeometry.isSimplyConnected_of_convex convex_strictRightHalfPlane
    ⟨1, by simp [strictRightHalfPlane]; norm_num⟩

/-- Absence of zeta zeros in the strict right half-plane. -/
def ZetaZeroFreeRight : Prop := ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0

theorem riemannHypothesis_iff_zetaZeroFreeRight : RiemannHypothesis ↔ ZetaZeroFreeRight := by
  rw [riemannHypothesis_iff_shellCriticalStripZeroFree (m := 12) le_rfl]
  constructor
  · intro h s hs hs1 hz
    by_cases hlt : s.re < 1
    · exact h s hs hlt (by rw [hz, zero_mul])
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hlt) hz
  · intro h s hs hlt
    refine mul_ne_zero (h s hs ?_) (shellMultiplier_ne_zero le_rfl hs)
    intro hc
    rw [hc] at hlt
    norm_num at hlt

theorem shellResidueUnit_ne_zero_of_zetaZeroFree {k : ℕ} (hk : 12 ≤ k)
    (hz : ZetaZeroFreeRight) {s : ℂ} (hs : 1 / 2 < s.re) : shellResidueUnit k s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1
    exact shellResidueUnit_one_ne_zero (by omega)
  · rw [shellResidueUnit]
    refine mul_ne_zero ?_ (shellMultiplier_ne_zero hk hs)
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.2 hs1) (hz s hs hs1)

/-- **The formation-potential criterion, holomorphy form.** -/
theorem riemannHypothesis_iff_analyticAt_survivalTransfer {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → AnalyticAt ℂ (survivalTransfer m r) s := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  constructor
  · intro hrh s hs
    have hz := riemannHypothesis_iff_zetaZeroFreeRight.1 hrh
    exact (analyticAt_shellSource_natCast_mul hm hr hs).div
      (analyticAt_shellResidueUnit hkm hs) (shellResidueUnit_ne_zero_of_zetaZeroFree hkm hz hs)
  · intro hana
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 hzero => ?_
    have hord := meromorphicOrderAt_survivalTransfer hm hr hρ hρ1
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
    have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hρ1, hzero⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt riemannZeta ρ = (n : ℕ∞) :=
      ⟨(analyticOrderAt riemannZeta ρ).toNat, (ENat.coe_toNat hfin).symm⟩
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [hn, h]; rfl) hne0
      · exact h
    have hanaR := hana ρ hρ
    have hordR : meromorphicOrderAt (survivalTransfer m r) ρ
        = ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (survivalTransfer m r) ρ) :=
      hanaR.meromorphicOrderAt_eq
    rw [hordR, hn] at hord
    obtain ⟨k, hk⟩ : ∃ k : ℕ∞, analyticOrderAt (survivalTransfer m r) ρ = k := ⟨_, rfl⟩
    rw [hk] at hord
    cases k with
    | top =>
        rw [ENat.map_top, ENat.map_coe] at hord
        exact absurd hord (not_eq_of_beq_eq_false rfl)
    | coe k =>
        simp only [ENat.map_coe] at hord
        have : ((k : ℤ) : WithTop ℤ) = -((n : ℤ) : WithTop ℤ) := by
          simpa using hord
        have hk' : (k : ℤ) = -(n : ℤ) := by exact_mod_cast this
        omega

/-- **The formation-potential criterion, holomorphy with nonvanishing.** -/
theorem riemannHypothesis_iff_analyticAt_and_ne_zero {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re → AnalyticAt ℂ (survivalTransfer m r) s ∧ survivalTransfer m r s ≠ 0 := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  constructor
  · intro hrh s hs
    have hz := riemannHypothesis_iff_zetaZeroFreeRight.1 hrh
    exact ⟨(riemannHypothesis_iff_analyticAt_survivalTransfer hm hr).1 hrh s hs,
      survivalTransfer_ne_zero hm hr hs (shellResidueUnit_ne_zero_of_zetaZeroFree hkm hz hs)⟩
  · intro h
    exact (riemannHypothesis_iff_analyticAt_survivalTransfer hm hr).2 fun s hs => (h s hs).1

/-- **Global exactness of renormalized formation work.**  The Riemann hypothesis is equivalent to
the existence of a holomorphic potential on the strict right half-plane. -/
theorem riemannHypothesis_iff_exists_formationPotential {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    RiemannHypothesis ↔ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ strictRightHalfPlane ∧
      ∀ s ∈ strictRightHalfPlane, survivalTransfer m r s = Complex.exp (-Φ s) := by
  constructor
  · intro hrh
    have hall := (riemannHypothesis_iff_analyticAt_and_ne_zero hm hr).1 hrh
    have hdiff : DifferentiableOn ℂ (survivalTransfer m r) strictRightHalfPlane := fun s hs =>
      ((hall s (mem_strictRightHalfPlane.1 hs)).1.differentiableAt).differentiableWithinAt
    have hne : ∀ s ∈ strictRightHalfPlane, survivalTransfer m r s ≠ 0 := fun s hs =>
      (hall s (mem_strictRightHalfPlane.1 hs)).2
    obtain ⟨f, hf, hfe⟩ := GaloisForLFunctions.HTGeometry.exists_differentiableOn_exp_eq
      isOpen_strictRightHalfPlane isSimplyConnected_strictRightHalfPlane hdiff hne
    exact ⟨fun s => -f s, hf.neg, fun s hs => by rw [neg_neg, hfe s hs]⟩
  · rintro ⟨Φ, hΦ, hΦe⟩
    refine (riemannHypothesis_iff_analyticAt_survivalTransfer hm hr).2 fun s hs => ?_
    have hmem : s ∈ strictRightHalfPlane := hs
    have hdiff : DifferentiableOn ℂ (fun z => Complex.exp (-Φ z)) strictRightHalfPlane :=
      fun z hz => ((hΦ z hz).neg).cexp
    have hana : AnalyticAt ℂ (fun z => Complex.exp (-Φ z)) s :=
      (hdiff.analyticOnNhd isOpen_strictRightHalfPlane) s hmem
    refine hana.congr ?_
    filter_upwards [isOpen_strictRightHalfPlane.mem_nhds hmem] with z hz
    exact (hΦe z hz).symm

/-! ## The branch-free charge form -/

/-- **Charge formula.**  At a strict-right zeta zero of multiplicity `q` the branch-free formation
work form `-d log R` has residue exactly `q`. -/
theorem residue_neg_logDeriv_survivalTransfer {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hzero : riemannZeta ρ = 0) :
    ∃ q : ℕ, 1 ≤ q ∧ analyticOrderAt riemannZeta ρ = (q : ℕ∞) ∧
      Tendsto (fun s => (s - ρ) * (-logDeriv (survivalTransfer m r) s)) (𝓝[≠] ρ)
        (𝓝 (q : ℂ)) := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hzero
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hρ1, hzero⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, analyticOrderAt riemannZeta ρ = (q : ℕ∞) :=
    ⟨(analyticOrderAt riemannZeta ρ).toNat, (ENat.coe_toNat hfin).symm⟩
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exact absurd (by rw [hq, h]; rfl) hne0
    · exact h
  refine ⟨q, hq1, hq, ?_⟩
  have hden : AnalyticAt ℂ (shellResidueUnit (r * m)) ρ := analyticAt_shellResidueUnit hkm hρ
  have hdenorder : analyticOrderAt (shellResidueUnit (r * m)) ρ = (q : ℕ∞) := by
    rw [analyticOrderAt_shellResidueUnit hkm hρ hρ1, hq]
  obtain ⟨g, hg, hg0, hfac⟩ := hden.analyticOrderAt_eq_natCast.1 hdenorder
  have hnum : AnalyticAt ℂ (fun z => shellSource m ((r : ℂ) * z)) ρ :=
    analyticAt_shellSource_natCast_mul hm hr hρ
  have hnum0 : shellSource m ((r : ℂ) * ρ) ≠ 0 := shellSource_natCast_mul_ne_zero hm hr hρ
  have hdenres : Tendsto (fun s => (s - ρ) * logDeriv (shellResidueUnit (r * m)) s)
      (𝓝[≠] ρ) (𝓝 (q : ℂ)) := logDeriv_residue_of_factorization hg hg0 hfac
  have hnumres : Tendsto (fun s => (s - ρ) * logDeriv (fun z => shellSource m ((r : ℂ) * z)) s)
      (𝓝[≠] ρ) (𝓝 0) := by
    have hcont : ContinuousAt (logDeriv (fun z => shellSource m ((r : ℂ) * z))) ρ :=
      (hnum.deriv.continuousAt).div hnum.continuousAt hnum0
    have ha : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
      ((continuous_id.sub continuous_const).tendsto' ρ 0 (by simp)).mono_left nhdsWithin_le_nhds
    have hb := hcont.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
    simpa using ha.mul hb
  have hcomb := hdenres.sub hnumres
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hg.eventually_analyticAt,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0),
    nhdsWithin_le_nhds hfac,
    nhdsWithin_le_nhds (hnum.continuousAt.eventually_ne hnum0),
    nhdsWithin_le_nhds hnum.eventually_analyticAt,
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ)]
    with s hs hgana hgne hfacs hnumne hnumana hsre
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 (by simpa using hs)
  have hdens : shellResidueUnit (r * m) s ≠ 0 := by
    rw [hfacs]
    exact smul_ne_zero (pow_ne_zero q hsρ) hgne
  have hdenana : AnalyticAt ℂ (shellResidueUnit (r * m)) s :=
    analyticAt_shellResidueUnit hkm hsre
  have hlog : logDeriv (survivalTransfer m r) s
      = logDeriv (fun z => shellSource m ((r : ℂ) * z)) s
        - logDeriv (shellResidueUnit (r * m)) s :=
    logDeriv_div s hnumne hdens hnumana.differentiableAt hdenana.differentiableAt
  rw [hlog]
  ring

/-- **The formation-potential criterion, charge-form version** (Theorem 4.1(4)).  The branch-free
work form is holomorphic on the strict right half-plane exactly under RH. -/
theorem riemannHypothesis_iff_analyticAt_logDeriv {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re → AnalyticAt ℂ (logDeriv (survivalTransfer m r)) s := by
  constructor
  · intro hrh s hs
    obtain ⟨hana, hne⟩ := (riemannHypothesis_iff_analyticAt_and_ne_zero hm hr).1 hrh s hs
    exact hana.deriv.div hana hne
  · intro hform
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 hzero => ?_
    obtain ⟨q, hq1, -, hres⟩ := residue_neg_logDeriv_survivalTransfer hm hr hρ hzero
    have hcont : ContinuousAt (fun s => (s - ρ) * (-logDeriv (survivalTransfer m r) s)) ρ :=
      ((continuous_id.sub continuous_const).continuousAt).mul
        ((hform ρ hρ).continuousAt.neg)
    have hzerolim : Tendsto (fun s => (s - ρ) * (-logDeriv (survivalTransfer m r) s))
        (nhdsWithin ρ {ρ}ᶜ) (nhds 0) := by
      have h := hcont.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
      simpa using h
    have hne : (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)).NeBot := by
      exact NormedField.nhdsNE_neBot ρ
    have := tendsto_nhds_unique hres hzerolim
    have hq0 : (q : ℂ) = 0 := this
    have : q = 0 := by exact_mod_cast hq0
    omega

/-- **Constructive Kummer descent.**  When `n` divides the order, the root history descends to a
single-valued meromorphic `n`-th root on the base disk. -/
theorem exists_meromorphic_root_of_dvd {R u : ℂ → ℂ} {z₀ : ℂ} {q : ℤ} {n : ℕ} (hn : n ≠ 0)
    (hu : AnalyticAt ℂ u z₀) (hu0 : u z₀ ≠ 0)
    (hR : R =ᶠ[nhdsWithin z₀ {z₀}ᶜ] fun z => (z - z₀) ^ q * u z)
    (hdvd : (n : ℤ) ∣ q) :
    ∃ G : ℂ → ℂ, MeromorphicAt G z₀ ∧ (G ^ n) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] R := by
  obtain ⟨k, rfl⟩ := hdvd
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball z₀ ε, AnalyticAt ℂ u z ∧ u z ≠ 0 := by
    have h1 := hu.eventually_analyticAt
    have h2 := hu.continuousAt.eventually_ne hu0
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
    exact ⟨ε, hε, fun z hz => hsub hz⟩
  have hUo : IsOpen (Metric.ball z₀ ε) := Metric.isOpen_ball
  have hUsc : IsSimplyConnected (Metric.ball z₀ ε) :=
    GaloisForLFunctions.HTGeometry.isSimplyConnected_of_convex (convex_ball z₀ ε)
      ⟨z₀, Metric.mem_ball_self hε⟩
  have hdiff : DifferentiableOn ℂ u (Metric.ball z₀ ε) := fun z hz =>
    ((hball z hz).1.differentiableAt).differentiableWithinAt
  obtain ⟨L, hL, hLe⟩ := GaloisForLFunctions.HTGeometry.exists_differentiableOn_exp_eq hUo hUsc
    hdiff (fun z hz => (hball z hz).2)
  refine ⟨fun z => (z - z₀) ^ k * Complex.exp (L z / n), ?_, ?_⟩
  · have h1 : MeromorphicAt (fun z : ℂ => (z - z₀) ^ k) z₀ :=
      ((analyticAt_id.sub analyticAt_const).meromorphicAt).zpow k
    have h2 : MeromorphicAt (fun z : ℂ => Complex.exp (L z / n)) z₀ := by
      have hLa : AnalyticAt ℂ L z₀ :=
        (hL.analyticOnNhd hUo) z₀ (Metric.mem_ball_self hε)
      exact ((hLa.div_const).cexp).meromorphicAt
    exact h1.mul h2
  · filter_upwards [hR, nhdsWithin_le_nhds (hUo.mem_nhds (Metric.mem_ball_self hε)),
      self_mem_nhdsWithin] with z hz hzU hzne
    have hzz : z - z₀ ≠ 0 := sub_ne_zero.2 (by simpa using hzne)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    show ((z - z₀) ^ k * Complex.exp (L z / n)) ^ n = R z
    rw [hz, mul_pow, ← zpow_natCast ((z - z₀) ^ k) n, ← zpow_mul, ← Complex.exp_nat_mul]
    rw [show (n : ℂ) * (L z / n) = L z from by field_simp, hLe z hzU]
    congr 2
    ring

/-! ## Divisible-lift selection -/

/-- **Lemma 5.1, local form.**  Meromorphic roots at unbounded depths, valid only near the point,
still annihilate a finite meromorphic order. -/
theorem meromorphicOrderAt_eq_zero_of_eventual_roots {R : ℂ → ℂ} {z : ℂ}
    (hfinite : meromorphicOrderAt R z ≠ ⊤)
    (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : ℂ → ℂ, MeromorphicAt G z ∧
      (G ^ n) =ᶠ[nhdsWithin z {z}ᶜ] R) :
    meromorphicOrderAt R z = 0 := by
  have hRfinite := hfinite
  lift meromorphicOrderAt R z to ℤ using hfinite with q hq
  have hq0 : q = 0 := by
    refine GaloisForLFunctions.HTGeometry.int_eq_zero_of_unbounded_natCast_dvd q fun N => ?_
    obtain ⟨n, hn, G, hGmero, hGpow⟩ := hroot (max N 1)
    have hnN : N ≤ n := le_trans (le_max_left N 1) hn
    have hn0 : n ≠ 0 := by omega
    have horder : meromorphicOrderAt R z = (n : WithTop ℤ) * meromorphicOrderAt G z := by
      rw [← meromorphicOrderAt_congr hGpow]
      exact meromorphicOrderAt_pow hGmero
    have hGfinite : meromorphicOrderAt G z ≠ ⊤ := by
      intro htop
      rw [htop] at horder
      simp [hn0] at horder
      exact hRfinite (hq.trans horder)
    lift meromorphicOrderAt G z to ℤ using hGfinite with p hp
    refine ⟨n, hnN, ⟨p, ?_⟩⟩
    have hcast : (q : WithTop ℤ) = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by
      calc
        (q : WithTop ℤ) = meromorphicOrderAt R z := hq
        _ = (n : WithTop ℤ) * (p : WithTop ℤ) := horder
        _ = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by norm_cast
    exact_mod_cast hcast
  exact_mod_cast hq0

/-- **Divisible formation selection law.**  The Riemann hypothesis, the existence of a coherent
rational-power lift, holomorphic roots at every depth, and meromorphic roots along an unbounded
set of depths are the same condition. -/
theorem riemannHypothesis_tfae_divisibleLift {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) :
    List.TFAE
      [ RiemannHypothesis,
        ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ strictRightHalfPlane ∧
          ∀ s ∈ strictRightHalfPlane, survivalTransfer m r s = Complex.exp (-Φ s),
        ∀ n : ℕ, 1 ≤ n → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G strictRightHalfPlane ∧
          ∀ s ∈ strictRightHalfPlane, G s ^ n = survivalTransfer m r s,
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : ℂ → ℂ,
          (∀ s ∈ strictRightHalfPlane, MeromorphicAt G s) ∧
          ∀ s ∈ strictRightHalfPlane, G s ^ n = survivalTransfer m r s ] := by
  tfae_have 1 → 2 := (riemannHypothesis_iff_exists_formationPotential hm hr).1
  tfae_have 2 → 3 := by
    rintro ⟨Φ, hΦ, hΦe⟩ n hn
    refine ⟨fun s => Complex.exp (-Φ s / n), fun s hs => ?_, fun s hs => ?_⟩
    · exact (((hΦ s hs).neg).div_const _).cexp
    · rw [← Complex.exp_nat_mul, hΦe s hs]
      congr 1
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      field_simp
  tfae_have 3 → 4 := by
    intro h N
    obtain ⟨G, hG, hGe⟩ := h (max N 1) (le_max_right N 1)
    have hana : AnalyticOnNhd ℂ G strictRightHalfPlane :=
      hG.analyticOnNhd isOpen_strictRightHalfPlane
    exact ⟨max N 1, le_max_left N 1, G, fun s hs => (hana s hs).meromorphicAt, hGe⟩
  tfae_have 4 → 1 := by
    intro h
    refine (riemannHypothesis_iff_zetaZeroFreeRight).2 fun ρ hρ hρ1 hzero => ?_
    have hmem : ρ ∈ strictRightHalfPlane := hρ
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
    have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hρ1, hzero⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, analyticOrderAt riemannZeta ρ = (q : ℕ∞) :=
      ⟨(analyticOrderAt riemannZeta ρ).toNat, (ENat.coe_toNat hfin).symm⟩
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with hh | hh
      · exact absurd (by rw [hq, hh]; rfl) hne0
      · exact hh
    have hord := meromorphicOrderAt_survivalTransfer hm hr hρ hρ1
    rw [hq] at hord
    have hordfin : meromorphicOrderAt (survivalTransfer m r) ρ ≠ ⊤ := by
      rw [hord]
      simp
    have hzeroorder : meromorphicOrderAt (survivalTransfer m r) ρ = 0 := by
      refine meromorphicOrderAt_eq_zero_of_eventual_roots hordfin fun N => ?_
      obtain ⟨n, hn, G, hGm, hGe⟩ := h N
      refine ⟨n, hn, G, hGm ρ hmem, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (isOpen_strictRightHalfPlane.mem_nhds hmem)] with s hs
      exact hGe s hs
    rw [hzeroorder] at hord
    have hmap : ENat.map (Nat.cast : ℕ → ℤ) ((q : ℕ∞)) = 0 := neg_eq_zero.1 hord.symm
    rw [ENat.map_coe] at hmap
    have hq0 : (q : ℤ) = 0 := by exact_mod_cast hmap
    omega
  tfae_finish

/-- **Charge-divisibility conservation.**  Every root divides the branch-free charge form. -/
theorem logDeriv_survivalTransfer_eq_nsmul {m r : ℕ} {n : ℕ} {G : ℂ → ℂ} {s : ℂ}
    (hG : DifferentiableAt ℂ G s)
    (hGe : (fun z => G z ^ n) =ᶠ[nhds s] survivalTransfer m r) :
    logDeriv (survivalTransfer m r) s = (n : ℂ) * logDeriv G s := by
  have h1 : logDeriv (survivalTransfer m r) s = logDeriv (fun z => G z ^ n) s := by
    rw [logDeriv_apply, logDeriv_apply, hGe.deriv_eq, hGe.eq_of_nhds]
  rw [h1, logDeriv_fun_pow hG n]

/-- **Normalized formation potential** (DWP.16).  Under RH the potential can be pinned uniquely by
its value at the normalization point, which is the real number `log(H_{rm}(1)/S_m(r))`. -/
theorem exists_normalized_formationPotential {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r)
    (hrh : RiemannHypothesis) :
    ∃ (Φ : ℂ → ℂ) (S H : ℝ), 0 < S ∧ 0 < H ∧
      DifferentiableOn ℂ Φ strictRightHalfPlane ∧
      (∀ s ∈ strictRightHalfPlane, survivalTransfer m r s = Complex.exp (-Φ s)) ∧
      survivalTransfer m r 1 = ((S / H : ℝ) : ℂ) ∧
      Φ 1 = ((Real.log (H / S) : ℝ) : ℂ) := by
  obtain ⟨Φ₀, hΦ₀, hΦ₀e⟩ := (riemannHypothesis_iff_exists_formationPotential hm hr).1 hrh
  obtain ⟨S, H, hS, hH, -, -, hval, hlog⟩ := survivalTransfer_one_eq_ofReal_pos hm hr
  have hone : (1 : ℂ) ∈ strictRightHalfPlane := by
    simp [strictRightHalfPlane]
    norm_num
  set κ : ℂ := Φ₀ 1 - ((Real.log (H / S) : ℝ) : ℂ) with hκ
  have hexpLog : Complex.exp (-((Real.log (H / S) : ℝ) : ℂ)) = ((S / H : ℝ) : ℂ) := by
    have hpos : (0 : ℝ) < H / S := by positivity
    rw [← Complex.ofReal_neg, ← Real.log_inv, ← Complex.ofReal_exp, Real.exp_log (by positivity)]
    rw [inv_div]
  have hexpκ : Complex.exp κ = 1 := by
    have h1 : Complex.exp (-Φ₀ 1) = ((S / H : ℝ) : ℂ) := by
      rw [← hΦ₀e 1 hone, hval]
    have h2 : Complex.exp (-Φ₀ 1) = Complex.exp (-((Real.log (H / S) : ℝ) : ℂ)) := by
      rw [h1, hexpLog]
    have h3 : Complex.exp κ = Complex.exp (-((Real.log (H / S) : ℝ) : ℂ)) /
        Complex.exp (-Φ₀ 1) := by
      rw [← Complex.exp_sub, hκ]
      congr 1
      ring
    rw [h3, h2, div_self (Complex.exp_ne_zero _)]
  refine ⟨fun z => Φ₀ z - κ, S, H, hS, hH, hΦ₀.sub_const κ, fun s hs => ?_, hval, ?_⟩
  · rw [hΦ₀e s hs, show -(Φ₀ s - κ) = -Φ₀ s + κ from by ring, Complex.exp_add, hexpκ, mul_one]
  · simp only
    rw [hκ]
    ring

/-! ## Local Kummer descent -/

/-- A single-valued meromorphic `n`-th root forces `n` to divide the meromorphic order. -/
theorem dvd_meromorphicOrderAt_of_root {R G : ℂ → ℂ} {z : ℂ} {q : ℤ} {n : ℕ}
    (hG : MeromorphicAt G z) (hpow : (G ^ n) =ᶠ[nhdsWithin z {z}ᶜ] R)
    (hq : meromorphicOrderAt R z = (q : WithTop ℤ)) : (n : ℤ) ∣ q := by
  have horder : meromorphicOrderAt R z = (n : WithTop ℤ) * meromorphicOrderAt G z := by
    rw [← meromorphicOrderAt_congr hpow]
    exact meromorphicOrderAt_pow hG
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [horder] at hq
    simp only [Nat.cast_zero, zero_mul] at hq
    have : q = 0 := by exact_mod_cast hq.symm
    simp [this]
  have hGfinite : meromorphicOrderAt G z ≠ ⊤ := by
    intro htop
    rw [htop] at horder
    simp [hn0] at horder
    rw [horder] at hq
    exact absurd hq.symm (by simp)
  lift meromorphicOrderAt G z to ℤ using hGfinite with p hp
  refine ⟨p, ?_⟩
  have hcast : ((q : ℤ) : WithTop ℤ) = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by
    calc ((q : ℤ) : WithTop ℤ) = meromorphicOrderAt R z := hq.symm
      _ = (n : WithTop ℤ) * (p : WithTop ℤ) := horder
      _ = (((n : ℤ) * p : ℤ) : WithTop ℤ) := by norm_cast
  exact_mod_cast hcast

/-- **Deck holonomy of the root history** (DWP.24).  Continuing the branch `z^{q/n}·u^{1/n}` once
around the puncture multiplies it by `exp(2πiq/n)`. -/
theorem root_branch_loop_factor (q : ℤ) (n : ℕ) (L c : ℂ) :
    Complex.exp (((q : ℂ) / (n : ℂ)) * (L + 2 * Real.pi * Complex.I) + c)
      = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) / (n : ℂ)) *
        Complex.exp (((q : ℂ) / (n : ℂ)) * L + c) := by
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- **Trivial holonomy is exactly divisibility.** -/
theorem root_holonomy_eq_one_iff_dvd {q : ℤ} {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) / (n : ℂ)) = 1 ↔ (n : ℤ) ∣ q := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2πI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hq : (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (k : ℂ)) := by
      field_simp at hk
      linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
    exact_mod_cast mul_left_cancel₀ h2πI hq
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

end

end RHTower
