import GaloisForLFunctions.RHTower.WeilAbelianTwistPowerRigidity
import GaloisForLFunctions.HTGeometry.HalfPlaneBoundaryPrimitive
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Mixed spectra: non-integer spectral mass of order `T^α`, `α < 1`, forces `Λ` and RH

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_k c_k · 2(s−½)/((s−½)² + u_k²) + Φ_d(s)`.

The data are: integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`); real masses `c_k ≥ 0`
at ordinates `u_k ≥ 1`, `u_k → ∞`; and a diffuse part `Φ_d`, holomorphic with `Re Φ_d ≥ 0` on
`Re s > ½` and continuous up to the critical line.  Its boundary density is `Re Φ_d(½ + iv)/π`.

**Theorem** (`mixed_spectrum_power_rigidity`).  If the non-integer spectral mass below height `y`,

`C(y) = Σ_{u_k < y} c_k + (1/π) ∫_{−y}^{0} Re Φ_d(½ + iv) dv`,

is `O(y^α)` for some `α < 1`, then `lam(n) = Λ(n)` for every `n ≥ 2`, and RH holds.

**Evaporation** (`fractional_deficit_power_growth_rigidity`).  For real masses `0 ≤ c_k ≤ 1` the
reflection phase sees `c_k` only modulo `1`, so the downward lift `c_k − 1` may be used instead:
if the deficit `Σ_{u_k < y} (1 − c_k)` is `O(y^α)` for some `α < 1`, then `lam = Λ` and RH holds.
This covers zeros evaporated by `r_γ` with `Σ_{γ < T} r_γ = O(T^α)`.

**Proof.**
* `Φ_d(s̄) = conj Φ_d(s)` on `Re s ≥ ½` (`phid_conj`): on `Re s > 1` every other term of the identity
  has real coefficients; the identity theorem and continuity extend this.
* `H = exp P`, with `P` the boundary-continuous primitive of `Φ_d`
  (`HTGeometry.pathPrimitive`).  Then `H(s̄) = conj H(s)`, and on the line
  `H(½ − iy) = e^{−2i Im P(½ − iy)} conj H(½ − iy)`, where
  `Im P(½ − iy) = −∫_{−y}^{0} Re Φ_d(½ + iv) dv` by the boundary increment.
* `G = (K Q R) · H`, with `K Q R` the atomic producer (`FractionalMassTailRigidity.gInf`).  The
  lower-line lock is `G(1 − s) = e^{2πi C(y)} G(s)` with `C` monotone, and
  `AbelianTwist.abelian_twist_power_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity FractionalMassTailRigidity

noncomputable section

/-! ### Real coefficients -/

theorem natCast_cpow_conj (n : ℕ) (s : ℂ) : conj ((n : ℂ) ^ s) = (n : ℂ) ^ conj s := by
  have h := Complex.conj_cpow (n : ℂ) s (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast] at h
  rw [h, Complex.conj_conj]

theorem LSeries_lamTwo_conj (lam : ℕ → ℝ) (s : ℂ) :
    LSeries (lamTwo lam) (conj s) = conj (LSeries (lamTwo lam) s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, if_false, map_div₀, natCast_cpow_conj]
    congr 1
    unfold lamTwo
    split_ifs <;> simp

/-- The left side of the identity has real coefficients. -/
theorem weilDatum_conj (lam : ℕ → ℝ) (s : ℂ) :
    zetaArchimedeanDatum (conj s) + 1 / (conj s - 1) - LSeries (lamTwo lam) (conj s) =
      conj (zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s) := by
  have hd : Complex.digamma (conj s / 2) = conj (Complex.digamma (s / 2)) := by
    rw [← ReflectedDigammaAnomaly.digamma_conj, map_div₀, map_ofNat]
  simp only [zetaArchimedeanDatum, map_sub, map_add, map_div₀, map_one, Complex.conj_ofReal,
    map_ofNat, hd, LSeries_lamTwo_conj]

theorem atomicPairSeries_conj (a t : ℕ → ℝ) (s : ℂ) :
    atomicPairSeries a t (conj s) = conj (atomicPairSeries a t s) := by
  unfold atomicPairSeries
  rw [map_mul, Complex.conj_tsum]
  simp only [map_div₀, map_mul, map_sub, map_add, map_pow, map_one, map_ofNat,
    Complex.conj_ofReal]

theorem fracSeries_conj (c u : ℕ → ℝ) (s : ℂ) :
    (∑' k, (c k : ℂ) * (2 * (conj s - 1 / 2) / ((conj s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) =
      conj (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) := by
  rw [Complex.conj_tsum]
  congr 1
  funext k
  simp only [map_div₀, map_mul, map_sub, map_add, map_pow, map_one, map_ofNat,
    Complex.conj_ofReal]

/-- **The diffuse part has real coefficients** on the closed half-plane `Re s ≥ ½`. -/
theorem phid_conj {lam : ℕ → ℝ} {m : ℕ → ℕ} {t c u : ℕ → ℝ} {Φd : ℂ → ℂ}
    (hΦdd : DifferentiableOn ℂ Φd {s : ℂ | 1 / 2 < s.re})
    (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) : Φd (conj s) = conj (Φd s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ Φd ∘ (starRingEnd ℂ) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : conj z ∈ U := by simpa [hU] using hz
    have h := ((hΦdd (conj z) hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  have hright : ∀ z : ℂ, 1 < z.re → Φd (conj z) = conj (Φd z) := by
    intro z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    have e1 := hid z hz
    have e2 := hid (conj z) hz'
    have hΦ1 : Φd z = (zetaArchimedeanDatum z + 1 / (z - 1) - LSeries (lamTwo lam) z) -
        atomicPairSeries (fun j => Real.pi * m j) t z -
        ∑' k, (c k : ℂ) * (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (u k : ℂ) ^ 2)) := by
      rw [e1]; ring
    have hΦ2 : Φd (conj z) = (zetaArchimedeanDatum (conj z) + 1 / (conj z - 1) -
        LSeries (lamTwo lam) (conj z)) - atomicPairSeries (fun j => Real.pi * m j) t (conj z) -
        ∑' k, (c k : ℂ) * (2 * (conj z - 1 / 2) / ((conj z - 1 / 2) ^ 2 + (u k : ℂ) ^ 2)) := by
      rw [e2]; ring
    rw [hΦ2, hΦ1, weilDatum_conj, atomicPairSeries_conj, fracSeries_conj]
    simp only [map_sub]
  have heq : Φd =ᶠ[𝓝 2] g := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    simp only [hg, Function.comp_apply]
    rw [hright z hz, Complex.conj_conj]
  have hEq := (hΦdd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  -- extend to the closed half-plane by continuity
  have hgc : ContinuousOn g {z : ℂ | 1 / 2 ≤ z.re} := by
    refine Complex.continuous_conj.comp_continuousOn (hΦdc.comp Complex.continuous_conj.continuousOn
      fun z hz => ?_)
    show 1 / 2 ≤ (conj z).re
    simpa using hz
  have hclosed : EqOn Φd g {z : ℂ | 1 / 2 ≤ z.re} :=
    hEq.of_subset_closure hΦdc hgc (fun z (hz : 1 / 2 < z.re) => show 1 / 2 ≤ z.re from hz.le)
      (by rw [Complex.closure_setOf_lt_re])
  have := hclosed (show 1 / 2 ≤ (conj s).re by simpa using hs)
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  rw [this]


/-! ### The theorem -/

/-- `Re Φ_d ≥ 0` extends from `Re s > ½` to the closed half-plane. -/
theorem re_nonneg_of_closure {Φd : ℂ → ℂ} (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    0 ≤ (Φd s).re := by
  have hcl : IsClosed ({z : ℂ | 1 / 2 ≤ z.re} ∩ (fun z => (Φd z).re) ⁻¹' Ici 0) :=
    (Complex.continuous_re.comp_continuousOn hΦdc).preimage_isClosed_of_isClosed
      (isClosed_le continuous_const Complex.continuous_re) isClosed_Ici
  have hsub : {z : ℂ | 1 / 2 < z.re} ⊆ {z : ℂ | 1 / 2 ≤ z.re} ∩ (fun z => (Φd z).re) ⁻¹' Ici 0 :=
    fun z (hz : 1 / 2 < z.re) =>
      ⟨show (1 / 2 : ℝ) ≤ z.re from hz.le, show (Φd z).re ∈ Ici 0 from hΦdre z hz⟩
  have h := hcl.closure_subset_iff.mpr hsub
  rw [Complex.closure_setOf_lt_re] at h
  exact (h hs).2

/-- **The producer of a mixed spectrum.**  Integer atoms, real atoms with `Σ c_k/u_k² < ∞` and
a diffuse part continuous up to the line give a Herglotz producer `G = (K Q R)·e^{P}` whose
lower-line lock is `G(1 − s) = e^{iθ(y)} G(s)`, `s = ½ − iy`, with
`θ(y) = 2π Σ_{u_k<y} c_k + 2∫_{−y}^{0} Re Φ_d(½ + iv) dv`. -/
theorem exists_producer_of_mixed_spectrum {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}
    {Φd : ℂ → ℂ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hcs2 : Summable fun k => c k / u k ^ 2)
    (hΦdd : DifferentiableOn ℂ Φd {s : ℂ | 1 / 2 < s.re})
    (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s) :
    ∃ Φ G : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
      (∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
        LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s) ∧
      (∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) ∧
      (∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) ∧ G 2 = bigG lam 2 ∧
      ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
        cexp (((2 * Real.pi * phaseSum c u (-(2 * τ)) +
          2 * ∫ v in -(-(2 * τ))..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re : ℝ) : ℂ) * I) *
            G (lineS τ) := by
  have hpi := Real.pi_pos
  have hidT : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s := hid
  have hconj : ∀ z : ℂ, 1 / 2 ≤ z.re → Φd (conj z) = conj (Φd z) := fun z hz =>
    phid_conj hΦdd hΦdc hidT hz
  have hline_re : ∀ v : ℝ, 0 ≤ (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := fun v =>
    re_nonneg_of_closure hΦdc hΦdre (by simp)
  have hlc : Continuous fun v : ℝ => (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (hΦdc.comp_continuous (by fun_prop) fun v => ?_)
    show 1 / 2 ≤ ((1 / 2 : ℂ) + (v : ℂ) * I).re
    simp
  set D : ℝ → ℝ := fun y => ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re with hD
  have hD0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ D y := fun y hy =>
    intervalIntegral.integral_nonneg (by linarith) fun v _ => hline_re v
  -- the producer
  set P : ℂ → ℂ := pathPrimitive (1 / 2) 2 Φd with hP
  have hPc : Continuous P := continuous_pathPrimitive hΦdc
  set G : ℂ → ℂ := fun s => gInf lam m t c u s * cexp (P s) with hGdef
  set Φ : ℂ → ℂ := fun s => phiInf m t c u s + Φd s with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => by
    rw [hid s hs]; rfl
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2).add hΦdd
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs => by
    simp only [hΦdef, Complex.add_re]
    exact add_nonneg (re_phiInf_nonneg hc hu1 hut hcs2 hs) (hΦdre s hs)
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    (continuousAt_gInf hone hsum hc hu1 hut hcs2 hs).mul (hPc.cexp.continuousAt)
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := by
    intro s hs
    have h1 := hasDerivAt_gInf (lam := lam) hone hsum hc hu1 hut hcs2 hs
    have h2 := (hasDerivAt_pathPrimitive (by norm_num : (1 / 2 : ℝ) < 2) hΦdc hΦdd hs).cexp
    refine (h1.mul h2).congr_deriv ?_
    simp only [hΦdef, hGdef, hP]
    ring
  have hP2 : P 2 = 0 := by
    simp [hP, pathPrimitive]
  have hG2 : G 2 = bigG lam 2 := by
    simp only [hGdef, hP2, Complex.exp_zero, mul_one]
    exact gInf_two hone hsum hc hu1 hut hcs2
  -- the phase of the diffuse factor on the line
  have hPhalf : (P (1 / 2)).im = 0 := by
    have h := pathPrimitive_conj (a := 1 / 2) (b := 2) hconj (1 / 2 : ℂ)
    have hc12 : conj (1 / 2 : ℂ) = 1 / 2 := by apply Complex.ext <;> simp
    rw [hc12] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hPbd : ∀ y : ℝ, (P ((1 / 2 : ℂ) + ((-y : ℝ) : ℂ) * I)).im = -D y := by
    intro y
    have h := pathPrimitive_boundary_sub (by norm_num : (1 / 2 : ℝ) < 2) hΦdc hΦdd 0 (-y)
    have e0 : ((1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = 1 / 2 := by push_cast; ring
    have e1 : ((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = (1 / 2 : ℂ) + ((-y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e0, e1] at h
    have him := congrArg Complex.im h
    rw [Complex.sub_im, hPhalf, sub_zero] at him
    rw [him]
    have e2 : (I * ∫ v in (0 : ℝ)..-y, Φd (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)).im =
        ∫ v in (0 : ℝ)..-y, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
      have hint : IntervalIntegrable (fun v : ℝ => Φd (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I))
          MeasureTheory.volume 0 (-y) :=
        (hΦdc.comp_continuous (by fun_prop) fun v => by simp).intervalIntegrable _ _
      have h := Complex.reCLM.intervalIntegral_comp_comm hint
      simp only [Complex.reCLM_apply] at h
      rw [← h]
      congr 1; funext v; push_cast; ring_nf
    rw [e2, hD]
    simp only
    rw [intervalIntegral.integral_symm]
  refine ⟨Φ, G, hΦd, hΦre, hid', hGc, hGd, hG2, fun τ hτ0 => ?_⟩
  have hy : 0 < -(2 * τ) := by linarith
  have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
    rw [lineS_eq]; push_cast; ring
  have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
  have hgInf : gInf lam m t c u (1 - lineS τ) =
      cexp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I) *
        gInf lam m t c u (lineS τ) := by
    simp only [gInf]
    rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
      hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
    ring
  have hlineP : lineS τ = (1 / 2 : ℂ) + ((-(-(2 * τ)) : ℝ) : ℂ) * I := by
    rw [lineS_eq]; push_cast; ring
  have hH : cexp (P (1 - lineS τ)) =
      cexp (((2 * D (-(2 * τ)) : ℝ) : ℂ) * I) * cexp (P (lineS τ)) := by
    have hPc' : ∀ z, P (conj z) = conj (P z) := fun z => pathPrimitive_conj hconj z
    rw [one_sub_lineS_eq_conj, hPc', ← Complex.exp_add]
    congr 1
    have him := hPbd (-(2 * τ))
    rw [← hlineP] at him
    apply Complex.ext
    · simp
    · simp only [Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one]
      linarith
  simp only [hGdef]
  rw [hgInf, hH]
  have e : (((2 * Real.pi * phaseSum c u (-(2 * τ)) + 2 * D (-(2 * τ)) : ℝ) : ℂ) * I) =
      (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I) +
        (((2 * D (-(2 * τ)) : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [e, Complex.exp_add]
  ring

/-- **Mixed spectra.**  Integer atoms, real atoms and a diffuse part continuous up to the line:
if the non-integer spectral mass `C(y) = Σ_{u_k<y} c_k + (1/π)∫_{−y}^{0} Re Φ_d(½+iv) dv` is
`O(y^α)` for some `α < 1`, then `lam = Λ` and RH holds. -/
theorem mixed_spectrum_power_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}
    {Φd : ℂ → ℂ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hΦdd : DifferentiableOn ℂ Φd {s : ℂ | 1 / 2 < s.re})
    (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y →
      phaseSum c u y + (∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re) / Real.pi ≤
        K * y ^ α)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hpi := Real.pi_pos
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  have hline_re : ∀ v : ℝ, 0 ≤ (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := fun v =>
    re_nonneg_of_closure hΦdc hΦdre (by simp)
  have hlc : Continuous fun v : ℝ => (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (hΦdc.comp_continuous (by fun_prop) fun v => ?_)
    show 1 / 2 ≤ ((1 / 2 : ℂ) + (v : ℂ) * I).re
    simp
  set D : ℝ → ℝ := fun y => ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re with hD
  have hD0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ D y := fun y hy =>
    intervalIntegral.integral_nonneg (by linarith) fun v _ => hline_re v
  -- summability of the real masses
  have hcs2 : Summable fun k => c k / u k ^ 2 :=
    summable_div_sq_of_phaseSum_le hc hu1 hut (K := |K|) (K' := 0) fun y hy => by
      have h1 : y ^ α ≤ y := by
        calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy hα1.le
          _ = y := Real.rpow_one y
      have h0 : 0 ≤ y ^ α := Real.rpow_nonneg (by linarith) _
      have h2 : K * y ^ α ≤ |K| * y ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
      have h3 : 0 ≤ D y / Real.pi := div_nonneg (hD0 y (by linarith)) hpi.le
      have h4 := hCK y hy
      simp only [hD] at h3
      nlinarith [abs_nonneg K]
  obtain ⟨Φ, G, hΦd, hΦre, hid', hGc, hGd, hG2, hlock₀⟩ :=
    exists_producer_of_mixed_spectrum hone hsum hc hu1 hut hcs2 hΦdd hΦdc hΦdre hid
  -- the lock
  set C : ℝ → ℝ := fun x => phaseSum c u (2 * x) + D (2 * x) / Real.pi with hCdef
  have hDmono : Monotone fun y : ℝ => D (2 * y) := by
    intro a b hab
    simp only [hD]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hlc.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * b)) (-(2 * a)))
      (hlc.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * a)) 0)
    rw [← h]
    have : 0 ≤ ∫ v in -(2 * b)..-(2 * a), (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re :=
      intervalIntegral.integral_nonneg (by linarith) fun v _ => hline_re v
    linarith
  have hCm : Monotone C := fun a b hab => by
    have h1 := phaseSum_mono hc hut (show 2 * a ≤ 2 * b by linarith)
    have h2 := hDmono hab
    simp only [hCdef]
    have : D (2 * a) / Real.pi ≤ D (2 * b) / Real.pi := div_le_div_of_nonneg_right h2 hpi.le
    linarith
  have hCg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α := by
    refine ⟨α, K * 2 ^ α, hα1, fun x hx => ?_⟩
    have h := hCK (2 * x) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h
    simp only [hCdef, hD]; linarith
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((2 * Real.pi) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hCτ : C (-τ) = phaseSum c u (-(2 * τ)) + D (-(2 * τ)) / Real.pi := by
      simp only [hCdef]; ring_nf
    rw [hlock₀ τ hτ0, hCτ, one_mul]
    have e : 2 * Real.pi * (phaseSum c u (-(2 * τ)) + D (-(2 * τ)) / Real.pi) =
        2 * Real.pi * phaseSum c u (-(2 * τ)) + 2 * D (-(2 * τ)) := by
      field_simp
    rw [e]
  exact abelian_twist_power_rigidity hsl hΦd hΦre hid' hGc hGd hG2 hCm hCg hlock


/-! ### Evaporation: deficits below integer masses -/

/-- The number of atoms below any height is a natural number. -/
theorem exists_phaseSum_one_eq_nat {u : ℕ → ℝ} (hut : Tendsto u atTop atTop) (y : ℝ) :
    ∃ n : ℕ, phaseSum (fun _ => (1 : ℝ)) u y = n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually (eventually_ge_atTop y))
  refine ⟨((Finset.range N).filter (fun k => u k < y)).card, ?_⟩
  unfold phaseSum
  rw [tsum_eq_sum (s := Finset.range N) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk; rw [if_neg (not_lt.mpr (hN k hk))]]
  rw [Finset.sum_boole]

/-- **Evaporation with a power-saving deficit forces `Λ` and RH.**  The hypotheses of
`fractional_mass_power_growth_rigidity`, but with real masses `0 ≤ c_k ≤ 1` (for example evaporated
zeros of mass `1 − r_k`), `Σ_k c_k/u_k² < ∞`, and the *deficit* `Σ_{u_k < y} (1 − c_k) = O(y^α)` for
some `α < 1`.  The reflection phase sees each mass modulo `1`; the downward lift `c_k − 1` is
monotone and small. -/
theorem fractional_deficit_power_growth_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}
    {c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hcs2 : Summable fun k => c k / u k ^ 2)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y → phaseSum (fun k => 1 - c k) u y ≤ K * y ^ α)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  have hd0 : ∀ k, 0 ≤ 1 - c k := fun k => by linarith [hc1 k]
  set C : ℝ → ℝ := fun x => phaseSum (fun k => 1 - c k) u (2 * x) with hCdef
  have hCm : Monotone C := fun a b h => phaseSum_mono hd0 hut (by linarith)
  have hCg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α := by
    refine ⟨α, K * 2 ^ α, hα1, fun x hx => ?_⟩
    have h := hCK (2 * x) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h
    simp only [hCdef]; linarith
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((-(2 * Real.pi)) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) = cexp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I) *
        G (lineS τ) := by
      simp only [hGdef, gInf]
      rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
        hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
      ring
    obtain ⟨n, hn⟩ := exists_phaseSum_one_eq_nat hut (-(2 * τ))
    have hadd : phaseSum c u (-(2 * τ)) + phaseSum (fun k => 1 - c k) u (-(2 * τ)) = n := by
      rw [← hn]
      unfold phaseSum
      rw [← (summable_phaseTerm hut _).tsum_add (summable_phaseTerm hut _)]
      exact tsum_congr fun k => by split_ifs <;> ring
    have hCτ : C (-τ) = phaseSum (fun k => 1 - c k) u (-(2 * τ)) := by
      simp only [hCdef]; congr 1; ring
    rw [hrefl, hCτ, one_mul]
    congr 1
    have e : ((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I =
        (n : ℂ) * (2 * (Real.pi : ℂ) * I) +
          (((-(2 * Real.pi)) * phaseSum (fun k => 1 - c k) u (-(2 * τ)) : ℝ) : ℂ) * I := by
      have : phaseSum c u (-(2 * τ)) = n - phaseSum (fun k => 1 - c k) u (-(2 * τ)) := by
        linarith
      rw [this]; push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]
  exact abelian_twist_power_rigidity hsl hΦd hΦre hid' hGc hGd hG2 hCm hCg hlock

end

end AbelianTwist

end RHTower
