import GaloisForLFunctions.SquareRootThreshold.UnimodularTwoBumpTestsDecideTheCriticalLine

/-!
# The Weil form determines the configuration

Two tempered configurations whose Weil forms agree on the modulated two-bump tests
`κ_γ(t + v/2) + τ κ_γ(t − v/2)` are equal: same zeros, same multiplicities
(`eq_of_weil_twoBump_eq`). In particular the Weil form on compactly supported `C²` tests
determines the configuration (`eq_of_weil_eq`).

* **Polarization** (`lagStructure_eq_of_weil_twoBump_eq`). The values at `τ = 0, 1, i` recover the
  lag structures `S_γ(v)` for every height `γ` and lag `v`.
* **Signed configuration.** The difference `S_γ − S'_γ` is the lag structure of the signed
  multiplicity `c = m_Z − m_{Z'}` (`lagStructure_sub_eq`). It vanishes identically.
* **Off-line coefficients** (`multDiff_eq_zero_of_right`). Right of the line the signed sum is an
  exponential sum `Σ_t c_t Q_t e^{(δ_t + iγ_t)v}`, bounded for `v ≥ 0` by the other two parts. At
  the rightmost nonzero coefficient on a horizontal line it would have a pole that a bounded sum
  cannot have (`eq_zero_of_norm_tsum_exp_le`). So `c = 0` off the line.
* **On-line coefficients** (`multDiff_eq_zero_of_onLine`). What remains is
  `Σ_ρ c_ρ |h_γ(γ_ρ)|² e^{iγ_ρ v} = 0`. Its Cesàro means against `e^{−iγ₀v}` along a grid
  avoiding the countably many resonances isolate `c_{ρ₀} |κ̂(0)|²`.

The zero side alone is spectrally faithful: no two tempered configurations share a Weil form,
whatever their density and however their zeros are placed.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The signed multiplicity `m_Z − m_{Z'}`, each multiplicity extended by `0` off its carrier. -/
def multDiff (Z Z' : ZeroConfig) (z : ℂ) : ℂ :=
  Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z -
    Z'.carrier.indicator (fun z => (Z'.mult z : ℂ)) z

/-- The lag summand of a zero `z` with coefficient `c(z)`. -/
def coefTerm (c : ℂ → ℂ) (b : ℝ → ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  c z * paperFT (EF.weilTest b b) (gammaOf z) * cexp (I * gammaOf z * v)

theorem multDiff_reflect (Z Z' : ZeroConfig) (z : ℂ) :
    multDiff Z Z' (reflect z) = multDiff Z Z' z := by
  have h : ∀ W : ZeroConfig, W.carrier.indicator (fun z => (W.mult z : ℂ)) (reflect z) =
      W.carrier.indicator (fun z => (W.mult z : ℂ)) z := fun W => by
    by_cases hz : z ∈ W.carrier
    · rw [Set.indicator_of_mem ((reflect_mem_iff W z).mpr hz), Set.indicator_of_mem hz,
        W.mult_reflect z hz]
    · rw [Set.indicator_of_notMem (mt (reflect_mem_iff W z).mp hz), Set.indicator_of_notMem hz]
  rw [multDiff, multDiff, h Z, h Z']

theorem conj_multDiff (Z Z' : ZeroConfig) (z : ℂ) : conj (multDiff Z Z' z) = multDiff Z Z' z := by
  have h : ∀ W : ZeroConfig, conj (W.carrier.indicator (fun z => (W.mult z : ℂ)) z) =
      W.carrier.indicator (fun z => (W.mult z : ℂ)) z := fun W => by
    by_cases hz : z ∈ W.carrier
    · rw [Set.indicator_of_mem hz, Complex.conj_natCast]
    · rw [Set.indicator_of_notMem hz, map_zero]
  rw [multDiff, map_sub, h Z, h Z']

theorem mem_carrier_of_multDiff_ne_zero {Z Z' : ZeroConfig} {z : ℂ} (h : multDiff Z Z' z ≠ 0) :
    z ∈ Z.carrier ∪ Z'.carrier := by
  by_contra hz
  rw [Set.mem_union, not_or] at hz
  exact h (by rw [multDiff, Set.indicator_of_notMem hz.1, Set.indicator_of_notMem hz.2, sub_zero])

/-- A summand as coefficient, pair weight, growth and phase. -/
theorem coefTerm_eq_weight {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (c : ℂ → ℂ) (t : ℂ) (v : ℝ) :
    coefTerm c b v t = c t * pairWeight b (t.re - 1 / 2) t.im *
      (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) := by
  obtain ⟨h1, -⟩ := pair_summand hb hbc t.im (t.re - 1 / 2) v
  rw [← eq_heightPoint t] at h1
  have hI : I * I = -1 := Complex.I_mul_I
  have hexp : cexp (I * ((t.im : ℂ) - I * ((t.re - 1 / 2 : ℝ) : ℂ)) * (v : ℂ)) =
      cexp (((t.re - 1 / 2) * v : ℝ)) * cexp (I * t.im * v) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(((t.re : ℂ) - 1 / 2) * (v : ℂ))) * hI
  rw [coefTerm, mul_assoc, h1, hexp, Complex.ofReal_exp]
  ring

/-- The reflected summand carries the conjugate weight and the decaying growth. -/
theorem coefTerm_reflect_eq_weight {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (c : ℂ → ℂ) (t : ℂ) (v : ℝ) :
    coefTerm c b v (reflect t) = c (reflect t) * conj (pairWeight b (t.re - 1 / 2) t.im) *
      (Real.exp (-((t.re - 1 / 2) * v)) : ℂ) * cexp (I * t.im * v) := by
  obtain ⟨-, h2⟩ := pair_summand hb hbc t.im (t.re - 1 / 2) v
  rw [← reflect_eq_heightPoint t] at h2
  have hI : I * I = -1 := Complex.I_mul_I
  have hexp : cexp (I * ((t.im : ℂ) - I * ((-(t.re - 1 / 2) : ℝ) : ℂ)) * (v : ℂ)) =
      cexp ((-((t.re - 1 / 2) * v) : ℝ)) * cexp (I * t.im * v) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (((t.re : ℂ) - 1 / 2) * (v : ℂ)) * hI
  rw [coefTerm, mul_assoc, h2, hexp, Complex.ofReal_exp]
  ring

/-- On the line the summand is `c |h_b(γ)|² e^{iγv}`. -/
theorem coefTerm_onLine {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (c : ℂ → ℂ) {z : ℂ} (hz : z.re = 1 / 2) (v : ℝ) :
    coefTerm c b v z = c z * ((‖paperFT b z.im‖ ^ 2 : ℝ) : ℂ) * cexp (I * z.im * v) := by
  rw [coefTerm, gammaOf_eq_ofReal_of_re hz, EF.paperFT_weilTest hb hb hbc hbc, Complex.conj_ofReal,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The signed lag structure.** `S_Z − S_{Z'}` is the lag structure of `m_Z − m_{Z'}`. -/
theorem lagStructure_sub_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    Summable (coefTerm (multDiff Z Z') b v) ∧
      lagStructure Z b v - lagStructure Z' b v = ∑' z, coefTerm (multDiff Z Z') b v z := by
  have h1 : Summable (Z.carrier.indicator (lagTerm Z b v)) :=
    summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs v)
  have h2 : Summable (Z'.carrier.indicator (lagTerm Z' b v)) :=
    summable_subtype_iff_indicator.mp (summable_lagStructure Z' hZ' hb hbs v)
  have hpt : ∀ z, Z.carrier.indicator (lagTerm Z b v) z - Z'.carrier.indicator (lagTerm Z' b v) z =
      coefTerm (multDiff Z Z') b v z := fun z => by
    have h : ∀ W : ZeroConfig, W.carrier.indicator (lagTerm W b v) z =
        W.carrier.indicator (fun z => (W.mult z : ℂ)) z * paperFT (EF.weilTest b b) (gammaOf z) *
          cexp (I * gammaOf z * v) := fun W => by
      by_cases hz : z ∈ W.carrier
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, lagTerm]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, zero_mul]
    rw [h Z, h Z', coefTerm, multDiff]
    ring
  refine ⟨(h1.sub h2).congr hpt, ?_⟩
  have e1 := tsum_subtype Z.carrier (lagTerm Z b v)
  have e2 := tsum_subtype Z'.carrier (lagTerm Z' b v)
  rw [lagStructure, lagStructure, show (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b)
      (gammaOf ρ) * cexp (I * gammaOf ρ * v)) = ∑' ρ : Z.carrier, lagTerm Z b v ρ from rfl,
    show (∑' ρ : Z'.carrier, (Z'.mult ρ : ℂ) * paperFT (EF.weilTest b b)
      (gammaOf ρ) * cexp (I * gammaOf ρ * v)) = ∑' ρ : Z'.carrier, lagTerm Z' b v ρ from rfl,
    e1, e2, ← Summable.tsum_sub h1 h2]
  exact tsum_congr hpt

/-- **Polarization at one lag.** Agreement of the Weil forms on the two-bump tests at lag `v` with
`τ = 0, 1, i` gives agreement of the lag structures at `v` and `−v`. -/
theorem lagStructure_eq_of_weil_twoBump_eq_at (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ)
    (hW : ∀ τ ∈ ({0, 1, I} : Set ℂ), Z.W (twoBump b v τ) (twoBump b v τ) =
      Z'.W (twoBump b v τ) (twoBump b v τ)) :
    lagStructure Z b v = lagStructure Z' b v ∧ lagStructure Z b (-v) = lagStructure Z' b (-v) := by
  have h0 := hW 0 (by simp)
  have h1 := hW 1 (by simp)
  have hi := hW I (by simp)
  rw [W_twoBump Z hZ hb hbs, W_twoBump Z' hZ' hb hbs] at h0 h1 hi
  simp only [norm_zero, norm_one, Complex.norm_I, map_zero, map_one, Complex.conj_I,
    Complex.ofReal_zero, Complex.ofReal_one] at h0 h1 hi
  have hII : I * I = -1 := Complex.I_mul_I
  refine ⟨?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * h1 + (-I / 2) * hi - (1 - I) * h0 +
      ((lagStructure Z b v - lagStructure Z' b v) -
        (lagStructure Z b (-v) - lagStructure Z' b (-v))) / 2 * hII
  · linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * hi - (1 + I) * h0 +
      ((lagStructure Z b (-v) - lagStructure Z' b (-v)) -
        (lagStructure Z b v - lagStructure Z' b v)) / 2 * hII

/-- **Polarization.** Agreement of the Weil forms on the two-bump tests at `τ = 0, 1, i` gives
agreement of the lag structures. -/
theorem lagStructure_eq_of_weil_twoBump_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hW : ∀ (v : ℝ) (τ : ℂ), Z.W (twoBump b v τ) (twoBump b v τ) =
      Z'.W (twoBump b v τ) (twoBump b v τ)) (v : ℝ) :
    lagStructure Z b v = lagStructure Z' b v :=
  (lagStructure_eq_of_weil_twoBump_eq_at Z Z' hZ hZ' hb hbs v fun τ _ => hW v τ).1

/-- **Splitting by the critical line.** A summable function on `ℂ` sums to its on-line part plus
the pair sums `f(z) + f(reflect z)` over the half-plane `Re z > ½`. -/
theorem tsum_split_reflect {f : ℂ → ℂ} (hf : Summable f) :
    Summable ({z : ℂ | 1 / 2 < z.re}.indicator fun z => f z + f (reflect z)) ∧
      ∑' z, f z = ∑' z, {z : ℂ | z.re = 1 / 2}.indicator f z +
        ∑' z, {z : ℂ | 1 / 2 < z.re}.indicator (fun z => f z + f (reflect z)) z := by
  set On : Set ℂ := {z | z.re = 1 / 2} with hOn
  set Rr : Set ℂ := {z | 1 / 2 < z.re} with hRr
  set Ll : Set ℂ := {z | z.re < 1 / 2} with hLl
  have hre : ∀ z : ℂ, (reflect z).re = 1 - z.re := fun z => by simp [reflect]
  set e := Function.Involutive.toPerm reflect Zeta23.reflect_reflect with he
  have hrefl : ∀ z, Ll.indicator f (e z) = Rr.indicator (fun t => f (reflect t)) z := by
    intro z
    have hiff : e z ∈ Ll ↔ z ∈ Rr := by
      simp only [he, Function.Involutive.coe_toPerm, hLl, hRr, Set.mem_setOf_eq, hre]
      constructor <;> intro h <;> linarith
    by_cases hz : z ∈ Rr
    · rw [Set.indicator_of_mem (hiff.mpr hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (mt hiff.mp hz), Set.indicator_of_notMem hz]
  have hR' : Summable (Rr.indicator fun t => f (reflect t)) := by
    rw [← funext hrefl]
    exact (e.summable_iff (f := Ll.indicator f)).mpr (hf.indicator Ll)
  have hsum : Summable (Rr.indicator fun z => f z + f (reflect z)) := by
    rw [Set.indicator_add]
    exact (hf.indicator Rr).add hR'
  refine ⟨hsum, ?_⟩
  have hdec : ∀ z, f z = On.indicator f z + (Rr.indicator f z + Ll.indicator f z) := by
    intro z
    rcases lt_trichotomy z.re (1 / 2) with h | h | h
    · rw [Set.indicator_of_notMem (show z ∉ On from fun h' => by simp [hOn] at h'; linarith),
        Set.indicator_of_notMem (show z ∉ Rr from fun h' => by simp [hRr] at h'; linarith),
        Set.indicator_of_mem (show z ∈ Ll from h)]
      ring
    · rw [Set.indicator_of_mem (show z ∈ On from h),
        Set.indicator_of_notMem (show z ∉ Rr from fun h' => by simp [hRr] at h'; linarith),
        Set.indicator_of_notMem (show z ∉ Ll from fun h' => by simp [hLl] at h'; linarith)]
      ring
    · rw [Set.indicator_of_notMem (show z ∉ On from fun h' => by simp [hOn] at h'; linarith),
        Set.indicator_of_mem (show z ∈ Rr from h),
        Set.indicator_of_notMem (show z ∉ Ll from fun h' => by simp [hLl] at h'; linarith)]
      ring
  have hLR : ∑' z, Ll.indicator f z = ∑' z, Rr.indicator (fun t => f (reflect t)) z := by
    rw [← Equiv.tsum_eq e]
    exact tsum_congr hrefl
  rw [tsum_congr hdec, Summable.tsum_add (hf.indicator On) ((hf.indicator Rr).add (hf.indicator Ll)),
    Summable.tsum_add (hf.indicator Rr) (hf.indicator Ll), hLR, Set.indicator_add,
    Summable.tsum_add (hf.indicator Rr) hR']

/-- **Off-line coefficients vanish.** If the lag structures of `κ` modulated to every height agree,
the signed multiplicity vanishes at every point right of the critical line. -/
theorem multDiff_eq_zero_of_right (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z')
    (hS : ∀ γ v : ℝ, lagStructure Z (modScaledBump 1 γ) v = lagStructure Z' (modScaledBump 1 γ) v)
    {t : ℂ} (ht : 1 / 2 < t.re) : multDiff Z Z' t = 0 := by
  classical
  by_contra hc
  set b := modScaledBump 1 t.im with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two 1 t.im
  have hbs := modScaledBump_support one_pos t.im
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set c := multDiff Z Z' with hcdef
  set Q : ℂ → ℂ := fun z => pairWeight b (z.re - 1 / 2) z.im with hQ
  set Rr : Set ℂ := {z | 1 / 2 < z.re} with hRr
  set On : Set ℂ := {z | z.re = 1 / 2} with hOn
  have hsum : ∀ v, Summable (coefTerm c b v) := fun v => (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).1
  have hD : ∀ v, ∑' z, coefTerm c b v z = 0 := fun v => by
    rw [← (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).2, hS, sub_self]
  have hE : ∀ (z : ℂ) (v : ℝ), ‖cexp (I * z.im * v)‖ = 1 := fun z v => by
    rw [show I * (z.im : ℂ) * (v : ℂ) = ((z.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- weights and their summability
  have hcQ : ∀ z, ‖c z * Q z‖ = ‖coefTerm c b 0 z‖ := fun z => by
    rw [coefTerm_eq_weight hb.continuous hbc, norm_mul, norm_mul, norm_mul]
    simp [hQ]
  have hRs : Summable (Rr.indicator fun z => ‖c z * Q z‖) := by
    refine Summable.of_norm_bounded (hsum 0).norm fun z => ?_
    by_cases hz : z ∈ Rr
    · rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hcQ]
    · rw [Set.indicator_of_notMem hz, norm_zero]; exact norm_nonneg _
  have hOs : Summable (On.indicator fun z => ‖coefTerm c b 0 z‖) :=
    (hsum 0).norm.indicator On
  set K := ∑' z, On.indicator (fun z => ‖coefTerm c b 0 z‖) z +
    ∑' z, Rr.indicator (fun z => ‖c z * Q z‖) z with hK
  -- the growing part is bounded
  set A : ℝ → ℂ := fun v => ∑' z, Rr.indicator (fun z => c z * Q z *
    (Real.exp ((z.re - 1 / 2) * v) : ℂ) * cexp (I * z.im * v)) z with hA
  have hAb : ∀ v : ℝ, 0 ≤ v → ‖A v‖ ≤ K := by
    intro v hv
    obtain ⟨hPs, hspl⟩ := tsum_split_reflect (hsum v)
    have hpair : ∀ z, coefTerm c b v z + coefTerm c b v (reflect z) =
        c z * Q z * (Real.exp ((z.re - 1 / 2) * v) : ℂ) * cexp (I * z.im * v) +
          c z * conj (Q z) * (Real.exp (-((z.re - 1 / 2) * v)) : ℂ) * cexp (I * z.im * v) :=
      fun z => by
        rw [coefTerm_eq_weight hb.continuous hbc, coefTerm_reflect_eq_weight hb.continuous hbc,
          hcdef, multDiff_reflect]
    set Bf : ℂ → ℂ := Rr.indicator fun z => c z * conj (Q z) *
      (Real.exp (-((z.re - 1 / 2) * v)) : ℂ) * cexp (I * z.im * v) with hBf
    have hBb : ∀ z, ‖Bf z‖ ≤ Rr.indicator (fun z => ‖c z * Q z‖) z := fun z => by
      by_cases hz : z ∈ Rr
      · rw [hBf, Set.indicator_of_mem hz, Set.indicator_of_mem hz, norm_mul, norm_mul, norm_mul,
          hE, mul_one, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), norm_mul]
        have hδ : 0 ≤ z.re - 1 / 2 := by have : 1 / 2 < z.re := hz; linarith
        have hle : Real.exp (-((z.re - 1 / 2) * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith [norm_nonneg (c z), norm_nonneg (Q z), mul_nonneg (norm_nonneg (c z)) (norm_nonneg (Q z))]
      · rw [hBf, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
    have hBs : Summable Bf := Summable.of_norm_bounded hRs hBb
    have hAs : Summable (Rr.indicator fun z => c z * Q z *
        (Real.exp ((z.re - 1 / 2) * v) : ℂ) * cexp (I * z.im * v)) := by
      have := hPs.sub hBs
      refine this.congr fun z => ?_
      by_cases hz : z ∈ Rr
      · rw [hBf, Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          hpair]
        ring
      · rw [hBf, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
          Set.indicator_of_notMem hz, sub_zero]
    have hRpair : ∑' z, Rr.indicator (fun z => coefTerm c b v z + coefTerm c b v (reflect z)) z =
        A v + ∑' z, Bf z := by
      rw [hA, ← Summable.tsum_add hAs hBs]
      refine tsum_congr fun z => ?_
      by_cases hz : z ∈ Rr
      · rw [hBf, Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz, hpair]
      · rw [hBf, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
          Set.indicator_of_notMem hz, add_zero]
    have hzero := hD v
    rw [hspl, hRpair] at hzero
    have hOn' : ‖∑' z, On.indicator (coefTerm c b v) z‖ ≤
        ∑' z, On.indicator (fun z => ‖coefTerm c b 0 z‖) z := by
      refine (norm_tsum_le_tsum_norm ((hsum v).indicator On).norm).trans
        (Summable.tsum_le_tsum (fun z => ?_) ((hsum v).indicator On).norm hOs)
      by_cases hz : z ∈ On
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          coefTerm_onLine hb.continuous hbc c hz, coefTerm_onLine hb.continuous hbc c hz,
          norm_mul, norm_mul, hE, norm_mul, norm_mul, hE]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
    have hBn : ‖∑' z, Bf z‖ ≤ ∑' z, Rr.indicator (fun z => ‖c z * Q z‖) z :=
      (norm_tsum_le_tsum_norm hBs.norm).trans (Summable.tsum_le_tsum hBb hBs.norm hRs)
    have hAeq : A v = -(∑' z, On.indicator (coefTerm c b v) z) - ∑' z, Bf z := by
      linear_combination hzero
    rw [hAeq, hK]
    calc ‖-(∑' z, On.indicator (coefTerm c b v) z) - ∑' z, Bf z‖
        ≤ ‖∑' z, On.indicator (coefTerm c b v) z‖ + ‖∑' z, Bf z‖ := by
          rw [sub_eq_add_neg, ← neg_add]
          rw [norm_neg]
          exact norm_add_le _ _
      _ ≤ _ := add_le_add hOn' hBn
  -- the exponential sum over the points of nonzero weight
  set S : Set ℂ := {z | 1 / 2 < z.re ∧ c z * Q z ≠ 0} with hSdef
  have hSc : S ⊆ Z.carrier ∪ Z'.carrier := fun z hz =>
    mem_carrier_of_multDiff_ne_zero (left_ne_zero_of_mul hz.2)
  haveI : Countable S :=
    (((carrier_countable Z).union (carrier_countable Z')).mono hSc).to_subtype
  set lamC : ℂ → ℂ := fun z => ((z.re - 1 / 2 : ℝ) : ℂ) + I * (z.im : ℂ) with hlamC
  set lam : S → ℂ := fun z => lamC z with hlamdef
  have hlre : ∀ z : S, (lam z).re = (z : ℂ).re - 1 / 2 := fun z => by simp [hlamdef, hlamC]
  have hlim : ∀ z : S, (lam z).im = (z : ℂ).im := fun z => by simp [hlamdef, hlamC]
  have hlam : ∀ z : S, 0 < (lam z).re ∧ (lam z).re ≤ 1 / 2 := fun z => by
    rw [hlre]
    have h1 : 1 / 2 < (z : ℂ).re := z.2.1
    have h2 : (z : ℂ).re ≤ 1 := by
      rcases hSc z.2 with h | h
      · exact (Z.strip _ h).2
      · exact (Z'.strip _ h).2
    constructor <;> linarith
  have hqS : Summable fun z : S => ‖c z * Q z‖ := by
    have h1 : Summable (S.indicator fun z => ‖c z * Q z‖) := by
      refine (hRs.indicator S).congr fun z => ?_
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
          Set.indicator_of_mem (show z ∈ Rr from hz.1)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    exact summable_subtype_iff_indicator.mpr h1
  -- the rightmost point of `S` at the height of `t`
  have hQt : Q t ≠ 0 := pairWeight_modScaledBump_ne_zero one_pos _ _
  have htS : t ∈ S := ⟨ht, mul_ne_zero hc hQt⟩
  have hfinw : ({z | z ∈ Z.carrier ∪ Z'.carrier ∧ t.im - 1 < z.im ∧ z.im ≤ t.im} : Set ℂ).Finite := by
    refine ((Z.finite_window (t.im - 1) t.im).union (Z'.finite_window (t.im - 1) t.im)).subset ?_
    rintro z ⟨hz | hz, h1, h2⟩
    · exact Or.inl ⟨hz, h1, h2⟩
    · exact Or.inr ⟨hz, h1, h2⟩
  set F := hfinw.toFinset.filter fun z => z ∈ S ∧ z.im = t.im with hF
  have hmemF : ∀ z ∈ S, z.im = t.im → z ∈ F := fun z hz him => by
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hSc hz, by linarith, by linarith⟩, hz, him⟩
  obtain ⟨t₀, ht₀F, htop⟩ := Finset.exists_max_image F (fun z => z.re) ⟨t, hmemF t htS rfl⟩
  rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at ht₀F
  obtain ⟨-, ht₀S, him₀⟩ := ht₀F
  obtain ⟨η₁, hη₁, hsep₁⟩ := exists_sep_height Z t.im
  obtain ⟨η₂, hη₂, hsep₂⟩ := exists_sep_height Z' t.im
  set T₀ : S := ⟨t₀, ht₀S⟩ with hT₀
  have hq0 := eq_zero_of_norm_tsum_exp_le (lam := lam) (q := fun z : S => c z * Q z) hqS hlam T₀
    (fun z him => by
      rw [hlre, hlre]
      rw [hlim, hlim] at him
      have := htop z (hmemF z z.2 (him.trans him₀))
      simpa [hT₀] using this)
    (fun z hl => by
      have hre := congrArg Complex.re hl
      have him := congrArg Complex.im hl
      rw [hlre, hlre] at hre
      rw [hlim, hlim] at him
      exact Subtype.ext (Complex.ext (by linarith) him))
    (lt_min hη₁ hη₂)
    (fun z hlt => by
      rw [hlim, hlim] at hlt ⊢
      have hlt' : |(z : ℂ).im - t.im| < min η₁ η₂ := by simpa [hT₀, him₀] using hlt
      have hz : (z : ℂ).im = t.im := by
        rcases hSc z.2 with h | h
        · exact hsep₁ _ h (hlt'.trans_le (min_le_left _ _))
        · exact hsep₂ _ h (hlt'.trans_le (min_le_right _ _))
      simpa [hT₀, him₀] using hz)
    (fun v hv => by
      refine le_of_eq_of_le (congrArg norm ?_) (hAb v hv)
      have h := tsum_subtype S fun z => c z * Q z * cexp (lamC z * v)
      rw [h]
      refine tsum_congr fun z => ?_
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Rr from hz.1), hlamC]
        simp only
        rw [add_mul, Complex.exp_add, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
        ring_nf
      · rw [Set.indicator_of_notMem hz]
        by_cases hR : z ∈ Rr
        · rw [Set.indicator_of_mem hR]
          have h0 : c z * Q z = 0 := by
            by_contra h0
            exact hz ⟨hR, h0⟩
          rw [h0, zero_mul, zero_mul]
        · rw [Set.indicator_of_notMem hR])
  exact ht₀S.2 hq0

/-- Off the line the signed multiplicity vanishes on both sides. -/
theorem multDiff_eq_zero_of_offLine (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z')
    (hS : ∀ γ v : ℝ, lagStructure Z (modScaledBump 1 γ) v = lagStructure Z' (modScaledBump 1 γ) v)
    {z : ℂ} (hz : z.re ≠ 1 / 2) : multDiff Z Z' z = 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · rw [← multDiff_reflect]
    exact multDiff_eq_zero_of_right Z Z' hZ hZ' hS (by simp [reflect]; linarith)
  · exact multDiff_eq_zero_of_right Z Z' hZ hZ' hS h

/-- **On-line coefficients vanish.** Once the off-line coefficients are gone, the signed lag
structure is `Σ_ρ c_ρ |h(γ_ρ)|² e^{iγ_ρ v}`; its Cesàro means against `e^{−iγ₀v}` along a
non-resonant grid isolate `c_{ρ₀} |κ̂(0)|²`. -/
theorem multDiff_eq_zero_of_onLine (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z')
    (hS : ∀ γ v : ℝ, lagStructure Z (modScaledBump 1 γ) v = lagStructure Z' (modScaledBump 1 γ) v)
    {ρ₀ : ℂ} (hρ₀ : ρ₀.re = 1 / 2) : multDiff Z Z' ρ₀ = 0 := by
  classical
  by_contra hc
  set γ₀ := ρ₀.im with hγ₀
  set b := modScaledBump 1 γ₀ with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two 1 γ₀
  have hbs := modScaledBump_support one_pos γ₀
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set c := multDiff Z Z' with hcdef
  set On : Set ℂ := {z | z.re = 1 / 2} with hOn
  set g : ℂ → ℂ := On.indicator fun z => c z * ((‖paperFT b z.im‖ ^ 2 : ℝ) : ℂ) with hg
  have hterm : ∀ (v : ℝ) (z : ℂ), coefTerm c b v z = g z * cexp (I * z.im * v) := by
    intro v z
    by_cases hz : z ∈ On
    · rw [hg, Set.indicator_of_mem hz, coefTerm_onLine hb.continuous hbc c hz]
    · rw [hg, Set.indicator_of_notMem hz, zero_mul, coefTerm,
        show c z = 0 from multDiff_eq_zero_of_offLine Z Z' hZ hZ' hS hz, zero_mul, zero_mul]
  have hgs : Summable fun z => ‖g z‖ := ((lagStructure_sub_eq Z Z' hZ hZ' hb hbs 0).1.norm).congr
    fun z => by rw [hterm]; simp
  have hD : ∀ v : ℝ, ∑' z, g z * cexp (I * z.im * v) = 0 := fun v => by
    rw [← tsum_congr (hterm v), ← (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).2, hS, sub_self]
  -- the weight at `ρ₀`
  have hκ : paperFT b γ₀ ≠ 0 := by
    have hmod : paperFT b γ₀ = paperFT (scaledBump 1) (((0 : ℝ) : ℂ) * I) := by
      rw [hbdef, show paperFT (modScaledBump 1 γ₀) γ₀ = paperFT (scaledBump 1) ((γ₀ : ℂ) - γ₀) from
        paperFT_modulate (scaledBump 1) γ₀ γ₀]
      simp
    rw [hmod]
    intro h
    have := norm_paperFT_scaledBump_I_mul_ge one_pos 0
    rw [h, norm_zero] at this
    have hpos : 0 < 4 * 1 * (Real.exp (-(1 * |(0 : ℝ)|)) * ∫ u, weilBump u) := by
      have := weilBump.integral_pos (μ := MeasureTheory.volume); positivity
    linarith
  have hg₀ : g ρ₀ ≠ 0 := by
    rw [hg, Set.indicator_of_mem (show ρ₀ ∈ On from hρ₀)]
    refine mul_ne_zero hc ?_
    exact_mod_cast (pow_pos (norm_pos_iff.mpr hκ) 2).ne'
  -- a non-resonant grid
  set Bad : Set ℝ := ⋃ z ∈ Z.carrier ∪ Z'.carrier,
    Set.range fun n : ℤ => 2 * π * n / (z.im - γ₀) with hBad
  have hBadc : Bad.Countable :=
    ((carrier_countable Z).union (carrier_countable Z')).biUnion fun z _ => Set.countable_range _
  obtain ⟨ℓ, ⟨hℓ0, -⟩, hℓB⟩ : (Set.Ioo (0 : ℝ) 1 \ Bad).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := MeasureTheory.volume)
    rw [MeasureTheory.measure_sdiff_null (hBadc.measure_zero _), Real.volume_Ioo]
    norm_num
  set wz : ℂ → ℂ := fun z => cexp (I * ((z.im - γ₀ : ℝ) : ℂ) * ℓ) with hwz
  have hwn : ∀ z, ‖wz z‖ = 1 := fun z => by
    show ‖cexp (I * ((z.im - γ₀ : ℝ) : ℂ) * ℓ)‖ = 1
    rw [show I * (((z.im - γ₀ : ℝ)) : ℂ) * (ℓ : ℂ) = (((z.im - γ₀) * ℓ : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hw1 : ∀ z, g z ≠ 0 → wz z = 1 → z = ρ₀ := by
    intro z hgz hw
    have hzOn : z.re = 1 / 2 := by
      by_contra h
      exact hgz (by rw [hg, Set.indicator_of_notMem (show z ∉ On from h)])
    have hcz : c z ≠ 0 := by
      intro h0
      exact hgz (by rw [hg, Set.indicator_of_mem (show z ∈ On from hzOn), h0, zero_mul])
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hw
    have hreal : (z.im - γ₀) * ℓ = 2 * π * n := by
      have h0 : I * ((((z.im - γ₀) * ℓ - 2 * π * n : ℝ)) : ℂ) = 0 := by
        push_cast
        push_cast at hn
        linear_combination hn
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h Complex.I_ne_zero
      · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h)
    have him : z.im = γ₀ := by
      by_contra hne
      have hne' : z.im - γ₀ ≠ 0 := sub_ne_zero.mpr hne
      refine hℓB (Set.mem_biUnion (mem_carrier_of_multDiff_ne_zero hcz) ⟨n, ?_⟩)
      show 2 * π * n / (z.im - γ₀) = ℓ
      rw [← hreal]
      field_simp
    exact Complex.ext (by rw [hzOn, hρ₀]) him
  -- Cesàro means
  have hsumk : ∀ k : ℕ, Summable fun z => g z * wz z ^ k := fun k =>
    Summable.of_norm_bounded hgs fun z => by rw [norm_mul, norm_pow, hwn, one_pow, mul_one]
  have hak : ∀ k : ℕ, ∑' z, g z * wz z ^ k = 0 := by
    intro k
    have h := hD (k * ℓ)
    have : (∑' z, g z * wz z ^ k) = cexp (-(I * γ₀ * ((k * ℓ : ℝ) : ℂ))) *
        ∑' z, g z * cexp (I * z.im * ((k * ℓ : ℝ) : ℂ)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun z => ?_
      simp only [hwz]
      rw [← Complex.exp_nat_mul, show cexp (-(I * γ₀ * ((k * ℓ : ℝ) : ℂ))) *
          (g z * cexp (I * z.im * ((k * ℓ : ℝ) : ℂ))) = g z * (cexp (-(I * γ₀ * ((k * ℓ : ℝ) : ℂ))) *
            cexp (I * z.im * ((k * ℓ : ℝ) : ℂ))) by ring, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [this, h, mul_zero]
  have hlim : Tendsto (fun N : ℕ => ∑' z, g z * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wz z ^ k))
      atTop (𝓝 (g ρ₀)) := by
    rw [← tsum_ite_eq ρ₀ g]
    refine tendsto_tsum_of_dominated_convergence hgs (fun z => ?_)
      (Eventually.of_forall fun N z => ?_)
    · by_cases hz : z = ρ₀
      · subst hz
        rw [if_pos rfl]
        have hw : wz z = 1 := by
          rw [hwz]
          simp [hγ₀]
        have : ∀ᶠ N : ℕ in atTop, g z * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wz z ^ k) = g z := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          rw [hw]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [inv_mul_cancel₀ (by exact_mod_cast (show N ≠ 0 by omega)), mul_one]
        exact tendsto_const_nhds.congr' (this.mono fun N h => h.symm)
      · rw [if_neg hz]
        by_cases hgz : g z = 0
        · simp [hgz]
        · have hw1' : wz z ≠ 1 := fun h => hz (hw1 z hgz h)
          simpa using (tendsto_geom_mean (hwn z).le hw1').const_mul (g z)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_geom_mean_le (hwn z).le N)
  have hzero : ∀ N : ℕ, ∑' z, g z * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wz z ^ k) = 0 := by
    intro N
    have : (∑' z, g z * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wz z ^ k)) =
        (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, ∑' z, g z * wz z ^ k := by
      rw [← Summable.tsum_finsetSum fun k _ => hsumk k, ← tsum_mul_left]
      refine tsum_congr fun z => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, Finset.sum_eq_zero fun k _ => hak k, mul_zero]
  exact hg₀ (tendsto_nhds_unique hlim (by simp_rw [hzero]; exact tendsto_const_nhds))

theorem hasCompactSupport_twoBump {b : ℝ → ℂ} (hbc : HasCompactSupport b) (v : ℝ) (τ : ℂ) :
    HasCompactSupport (twoBump b v τ) := by
  have h : twoBump b v τ = ∑ i : Fin 2, fun t => (![1, τ] i) * b (t - lagPoint 2 v i) := by
    funext t
    simp [twoBump, bumpTest, Finset.sum_apply]
  rw [h]
  exact HasCompactSupport.finset_sum fun i _ =>
    (hbc.comp_homeomorph (Homeomorph.subRight (lagPoint 2 v i))).mul_left
      (f := fun _ => ![1, τ] i)

/-- A vanishing signed multiplicity means equal configurations. -/
theorem eq_of_multDiff_eq_zero {Z Z' : ZeroConfig} (h0 : ∀ z, multDiff Z Z' z = 0) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  have hsub : ∀ {W W' : ZeroConfig}, (∀ z, multDiff W W' z = 0) →
      ∀ z ∈ W.carrier, z ∈ W'.carrier ∧ W.mult z = W'.mult z := by
    intro W W' h z hz
    have hz0 := h z
    rw [multDiff, Set.indicator_of_mem hz] at hz0
    by_cases hz' : z ∈ W'.carrier
    · rw [Set.indicator_of_mem hz', sub_eq_zero] at hz0
      exact ⟨hz', by exact_mod_cast hz0⟩
    · rw [Set.indicator_of_notMem hz', sub_zero] at hz0
      have := W.one_le_mult z hz
      have : (W.mult z : ℂ) ≠ 0 := by exact_mod_cast (show W.mult z ≠ 0 by omega)
      exact absurd hz0 this
  have h0' : ∀ z, multDiff Z' Z z = 0 := fun z => by
    have := h0 z
    rw [multDiff] at this ⊢
    linear_combination -this
  exact ⟨Set.ext fun z => ⟨fun h => (hsub h0 z h).1, fun h => (hsub h0' z h).1⟩,
    fun ρ hρ => (hsub h0 ρ hρ).2⟩

/-- **The Weil form on modulated two-bump tests determines the configuration.** Two tempered
configurations whose Weil forms agree on every `κ_γ(t + v/2) + τ κ_γ(t − v/2)` have the same
zeros with the same multiplicities. -/
theorem eq_of_weil_twoBump_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z')
    (hW : ∀ (γ v : ℝ) (τ : ℂ), Z.W (twoBump (modScaledBump 1 γ) v τ)
      (twoBump (modScaledBump 1 γ) v τ) =
        Z'.W (twoBump (modScaledBump 1 γ) v τ) (twoBump (modScaledBump 1 γ) v τ)) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  have hS : ∀ γ v : ℝ, lagStructure Z (modScaledBump 1 γ) v =
      lagStructure Z' (modScaledBump 1 γ) v := fun γ v =>
    lagStructure_eq_of_weil_twoBump_eq Z Z' hZ hZ' (contDiff_modScaledBump_two 1 γ)
      (modScaledBump_support one_pos γ) (hW γ) v
  have h0 : ∀ z, multDiff Z Z' z = 0 := fun z => by
    by_cases hz : z.re = 1 / 2
    · exact multDiff_eq_zero_of_onLine Z Z' hZ hZ' hS hz
    · exact multDiff_eq_zero_of_offLine Z Z' hZ hZ' hS hz
  exact eq_of_multDiff_eq_zero h0

/-- **The Weil form determines the configuration.** Two tempered configurations with the same
Weil form on compactly supported `C²` tests are equal. -/
theorem eq_of_weil_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ :=
  eq_of_weil_twoBump_eq Z Z' hZ hZ' fun γ v τ =>
    hW _ (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, τ])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support one_pos γ)) v τ)

end GaloisForLFunctions.SquareRootThreshold
