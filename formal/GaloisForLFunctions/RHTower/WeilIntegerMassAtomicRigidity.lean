import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule
import GaloisForLFunctions.RHTower.ZetaZerosBridge
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport
import GaloisForLFunctions.RHTower.CrystallineProducerRigidity

/-!
# Integer spectral masses force `Λ` and the Riemann hypothesis

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)`,
with integers `m_j ≥ 0`, ordinates `t_j ≥ 1` and `Σ_j m_j/t_j² < ∞`.  The right side is the
Herglotz function whose boundary measure on the critical line has mass `m_j` at `±t_j`.

**Theorem** (`integer_mass_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann
hypothesis holds.  The ordinates are arbitrary: they are not assumed to be zeta ordinates.

**Proof.**
* The genus-one canonical product `P` over `½ ± it_j` (multiplicity `m_j`) has `P'/P = Φ + B`,
  where `Φ` is the atomic series and `B = Σ m_j/(¼ + t_j²)`.  Put `Q = e^{−Bs}P`.
* `Φ` is odd under `s ↦ 1 − s`, so `Q(1−s) = Q(s)` (compare logarithmic derivatives on the strip
  `|Im s| < 1`, which contains no atom).
* `G(s) = s(s−1)Γ_ℝ(s) exp(Σ lam(n)n^{-s}/log n)` has `G'/G = Φ` on `Re s > 1`, so `G = K Q` there.
* `Re Φ ≥ 0` on `Re s ≥ ½`, so `|Q(σ+it)|` increases in `σ`; Stirling at `σ = 2` gives the decay
  needed by Hamburger's theorem on the critical line.
* Hamburger (`coeff_eq_of_critical_line_even_sublinear_defect`, zero defect) applied to the Dirichlet
  exponential of `lam/log` gives `exp(Σ lam(n)n^{-s}/log n) = ζ(s)`, hence `lam = Λ` on `n ≥ 2`.
* Then `KQ = s(s−1)Λ(s)`, whose zeros are the atoms `½ ± it_j`: the Riemann hypothesis.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace IntegerMassRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The atoms and their canonical product -/

/-- Atoms with multiplicity: index `j`, copy `k < m j`, and the side (`true` for `½ + it_j`). -/
abbrev AtomIndex (m : ℕ → ℕ) := Σ j : ℕ, Fin (m j) × Bool

/-- The atom `½ ± it_j`. -/
def atomAt (t : ℕ → ℝ) {m : ℕ → ℕ} (i : AtomIndex m) : ℂ :=
  if i.2.2 then atomPoint (t i.1) else atomMirror (t i.1)

theorem atomAt_re (t : ℕ → ℝ) {m : ℕ → ℕ} (i : AtomIndex m) : (atomAt t i).re = 1 / 2 := by
  unfold atomAt
  split_ifs
  · exact atomPoint_re _
  · exact atomMirror_re _

theorem atomAt_ne_zero (t : ℕ → ℝ) {m : ℕ → ℕ} (i : AtomIndex m) : atomAt t i ≠ 0 :=
  ne_zero_of_re_eq_half (atomAt_re t i)

theorem abs_im_atomAt (t : ℕ → ℝ) {m : ℕ → ℕ} (i : AtomIndex m) :
    |(atomAt t i).im| = |t i.1| := by
  unfold atomAt
  split_ifs <;> simp [atomPoint, atomMirror]

theorem norm_sq_atomAt (t : ℕ → ℝ) {m : ℕ → ℕ} (i : AtomIndex m) :
    ‖atomAt t i‖ ^ 2 = 1 / 4 + t i.1 ^ 2 := by
  unfold atomAt
  split_ifs <;>
  · rw [Complex.sq_norm, Complex.normSq_apply]
    simp [atomPoint, atomMirror]
    ring

theorem summable_inv_sq_atomAt {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) :
    Summable (fun i : AtomIndex m => 1 / ‖atomAt t i‖ ^ (2 : ℕ)) := by
  have hval : ∀ i : AtomIndex m, 1 / ‖atomAt t i‖ ^ (2 : ℕ) = 1 / (1 / 4 + t i.1 ^ 2) := by
    intro i; rw [norm_sq_atomAt]
  simp_rw [hval]
  refine (summable_sigma_of_nonneg (fun _ => by positivity)).mpr ⟨fun j => ?_, ?_⟩
  · exact (hasSum_fintype _).summable
  · have hin : ∀ j, ∑' _ : Fin (m j) × Bool, 1 / (1 / 4 + t j ^ 2) =
        2 * ((m j : ℝ) / (1 / 4 + t j ^ 2)) := by
      intro j
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      push_cast
      ring
    simp_rw [hin]
    refine (hsum.mul_left 2).of_nonneg_of_le (fun j => by positivity) fun j => ?_
    have htj : 0 < t j := by linarith [hone j]
    gcongr
    linarith

/-- The genus-one canonical product over the atoms. -/
def atomProduct (m : ℕ → ℕ) (t : ℕ → ℝ) : ℂ → ℂ :=
  canonicalProductE1Indexed (fun i : AtomIndex m => atomAt t i)

/-- The Mittag-Leffler constant `B = Σ_j m_j/(¼ + t_j²)`. -/
def atomConst (m : ℕ → ℕ) (t : ℕ → ℝ) : ℂ :=
  ∑' j, (m j : ℂ) / (1 / 4 + (t j : ℂ) ^ 2)

/-- The atoms of one pair contribute `2(z−½)/((z−½)² + t²) + 1/(¼ + t²)`. -/
theorem atom_pair_resolvent {t : ℝ} {z : ℂ} (h1 : z ≠ atomPoint t)
    (h2 : z ≠ atomMirror t) :
    (z - atomPoint t)⁻¹ + (atomPoint t)⁻¹ + ((z - atomMirror t)⁻¹ + (atomMirror t)⁻¹) =
      2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (t : ℂ) ^ 2) + 1 / (1 / 4 + (t : ℂ) ^ 2) := by
  have hP : atomPoint t ≠ 0 := ne_zero_of_re_eq_half (atomPoint_re t)
  have hM : atomMirror t ≠ 0 := ne_zero_of_re_eq_half (atomMirror_re t)
  have h1' : z - atomPoint t ≠ 0 := sub_ne_zero.mpr h1
  have h2' : z - atomMirror t ≠ 0 := sub_ne_zero.mpr h2
  have hprod : (z - atomPoint t) * (z - atomMirror t) = (z - 1 / 2) ^ 2 + (t : ℂ) ^ 2 :=
    sub_atomPoint_mul_sub_atomMirror z t
  have hPM : atomPoint t * atomMirror t = 1 / 4 + (t : ℂ) ^ 2 := by
    simp only [atomPoint, atomMirror]; ring_nf; rw [I_sq]; ring
  have hden : (z - 1 / 2) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by rw [← hprod]; exact mul_ne_zero h1' h2'
  have hden2 : (1 / 4 + (t : ℂ) ^ 2) ≠ 0 := by rw [← hPM]; exact mul_ne_zero hP hM
  rw [← hprod, ← hPM]
  field_simp
  simp only [atomPoint, atomMirror]
  ring

/-- **The Mittag-Leffler form of the atom product.**  Off the atoms,
`P'/P = 2(z−½) Σ_j m_j/((z−½)² + t_j²) + B`. -/
theorem logDeriv_atomProduct {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {z : ℂ}
    (hz : ∀ i : AtomIndex m, z ≠ atomAt t i) :
    logDeriv (atomProduct m t) z =
      atomicPairSeries (fun j => Real.pi * m j) t z + atomConst m t := by
  have hane := atomAt_ne_zero t (m := m)
  have hs2 := summable_inv_sq_atomAt hone hsum
  unfold atomProduct
  rw [logDeriv_canonicalProductE1Indexed hane hs2 hz]
  set f : AtomIndex m → ℂ := fun i => (z - atomAt t i)⁻¹ + (atomAt t i)⁻¹ with hf
  have hfs : Summable f := by
    have h := summable_canonicalProductE1LogDerivTerm hane hs2 hz
    refine h.neg.congr fun i => ?_
    simp only [hf]
    rw [show z - atomAt t i = -(atomAt t i - z) by ring, inv_neg]
    ring
  have hinner : ∀ j, ∑' c : Fin (m j) × Bool, f ⟨j, c⟩ =
      (m j : ℂ) * (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (t j : ℂ) ^ 2) +
        1 / (1 / 4 + (t j : ℂ) ^ 2)) := by
    intro j
    rw [tsum_fintype, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, hf, atomAt, if_true, Bool.false_eq_true, if_false]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
    · simp [h0]
    · have h1 : z ≠ atomPoint (t j) := by
        simpa [atomAt] using hz ⟨j, ⟨⟨0, hpos⟩, true⟩⟩
      have h2 : z ≠ atomMirror (t j) := by
        simpa [atomAt] using hz ⟨j, ⟨⟨0, hpos⟩, false⟩⟩
      rw [atom_pair_resolvent h1 h2]
  have hconst : Summable fun j => (m j : ℂ) * (1 / (1 / 4 + (t j : ℂ) ^ 2)) := by
    refine Summable.of_norm_bounded hsum fun j => ?_
    have htj : 0 < t j := by linarith [hone j]
    have hre : (1 / 4 + (t j : ℂ) ^ 2) = ((1 / 4 + t j ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hre, norm_mul, Complex.norm_natCast, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [mul_one_div]
    gcongr
    linarith
  have htot : Summable fun j => ∑' c : Fin (m j) × Bool, f ⟨j, c⟩ := hfs.sigma
  simp_rw [hinner] at htot
  have hpair : Summable fun j => (m j : ℂ) * (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) := by
    refine (htot.sub hconst).congr fun j => ?_
    ring
  rw [hfs.tsum_sigma]
  simp_rw [hinner]
  have hsplit : ∀ j, (m j : ℂ) * (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (t j : ℂ) ^ 2) +
      1 / (1 / 4 + (t j : ℂ) ^ 2)) = (m j : ℂ) * (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 + (t j : ℂ) ^ 2))
        + (m j : ℂ) * (1 / (1 / 4 + (t j : ℂ) ^ 2)) := fun j => by ring
  simp_rw [hsplit]
  rw [hpair.tsum_add hconst]
  congr 1
  · unfold atomicPairSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  · unfold atomConst
    refine tsum_congr fun j => ?_
    ring

/-- The atomic series is odd under `s ↦ 1 − s`. -/
theorem atomicPairSeries_one_sub (c t : ℕ → ℝ) (z : ℂ) :
    atomicPairSeries c t (1 - z) = -atomicPairSeries c t z := by
  unfold atomicPairSeries
  have h : (1 - z - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
  rw [h]
  ring

/-- `Q = e^{−Bs} P`. -/
def atomQ (m : ℕ → ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(atomConst m t * s)) * atomProduct m t s

theorem analyticOnNhd_atomQ {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) :
    AnalyticOnNhd ℂ (atomQ m t) Set.univ := by
  have hP := canonicalProductE1Indexed_analytic (fun i : AtomIndex m => atomAt t i)
    (atomAt_ne_zero t) (summable_inv_sq_atomAt hone hsum)
  have he : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp (-(atomConst m t * s))) Set.univ :=
    fun s _ => by fun_prop
  exact he.mul hP

theorem differentiable_atomQ {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) : Differentiable ℂ (atomQ m t) :=
  fun s => ((analyticOnNhd_atomQ hone hsum) s (Set.mem_univ s)).differentiableAt

theorem atomQ_ne_zero {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {z : ℂ}
    (hz : ∀ i : AtomIndex m, z ≠ atomAt t i) : atomQ m t z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _)
    (canonicalProductE1Indexed_ne_zero _ (atomAt_ne_zero t) (summable_inv_sq_atomAt hone hsum) hz)

theorem ne_atomAt_of_re_ne {t : ℕ → ℝ} {m : ℕ → ℕ} {z : ℂ} (hz : z.re ≠ 1 / 2) :
    ∀ i : AtomIndex m, z ≠ atomAt t i := fun i h => hz (h ▸ atomAt_re t i)

theorem ne_atomAt_of_abs_im_lt {t : ℕ → ℝ} {m : ℕ → ℕ} (hone : ∀ j, 1 ≤ t j) {z : ℂ}
    (hz : |z.im| < 1) : ∀ i : AtomIndex m, z ≠ atomAt t i := by
  intro i h
  have h1 := abs_im_atomAt t i
  rw [← h, abs_of_pos (by linarith [hone i.1] : 0 < t i.1)] at h1
  linarith [hone i.1]

theorem logDeriv_atomQ {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {z : ℂ}
    (hz : ∀ i : AtomIndex m, z ≠ atomAt t i) :
    logDeriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z := by
  have hP : atomProduct m t z ≠ 0 :=
    canonicalProductE1Indexed_ne_zero _ (atomAt_ne_zero t) (summable_inv_sq_atomAt hone hsum) hz
  have hPd : DifferentiableAt ℂ (atomProduct m t) z :=
    ((canonicalProductE1Indexed_analytic _ (atomAt_ne_zero t)
      (summable_inv_sq_atomAt hone hsum)) z (Set.mem_univ z)).differentiableAt
  have h := logDeriv_mul (f := fun s : ℂ => Complex.exp (-(atomConst m t * s)))
    (g := atomProduct m t) z (Complex.exp_ne_zero _) hP (by fun_prop) hPd
  unfold atomQ
  rw [h, logDeriv_atomProduct hone hsum hz]
  have he : logDeriv (fun s : ℂ => Complex.exp (-(atomConst m t * s))) z = -atomConst m t := by
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun s : ℂ => Complex.exp (-(atomConst m t * s)))
        (Complex.exp (-(atomConst m t * z)) * (-(atomConst m t))) z := by
      have := ((hasDerivAt_id z).const_mul (atomConst m t)).neg.cexp
      simpa using this
    rw [hd.deriv]
    field_simp [Complex.exp_ne_zero]
  rw [he]
  ring

/-- **The functional equation of the atom product.**  `Q(1−s) = Q(s)`. -/
theorem atomQ_one_sub {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (s : ℂ) :
    atomQ m t (1 - s) = atomQ m t s := by
  set U : Set ℂ := {z : ℂ | |z.im| < 1} with hU
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    simp only [hU, Set.mem_setOf_eq] at hx hy ⊢
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < 1 := by
        rcases eq_or_lt_of_le ha with ha0 | ha0
        · subst ha0; simp at hab; subst hab; simpa using hy
        · nlinarith [abs_nonneg x.im, abs_nonneg y.im]
  have hQd := differentiable_atomQ hone hsum
  have hne : ∀ z ∈ U, atomQ m t z ≠ 0 := fun z hz =>
    atomQ_ne_zero hone hsum (ne_atomAt_of_abs_im_lt hone hz)
  have hne' : ∀ z ∈ U, atomQ m t (1 - z) ≠ 0 := fun z hz =>
    hne (1 - z) (by simpa [hU] using hz)
  set r : ℂ → ℂ := fun z => atomQ m t (1 - z) / atomQ m t z with hr
  have hrd : DifferentiableOn ℂ r U := fun z hz =>
    (((hQd (1 - z)).comp z (by fun_prop)).div (hQd z) (hne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 U := by
    intro z hz
    have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_abs_im_lt hone hz
    have hz2 : ∀ i : AtomIndex m, 1 - z ≠ atomAt t i :=
      ne_atomAt_of_abs_im_lt hone (by simpa [hU] using hz)
    have hL1 := logDeriv_atomQ hone hsum hz1
    have hL2 := logDeriv_atomQ hone hsum hz2
    rw [logDeriv_apply] at hL1 hL2
    have hd1 : HasDerivAt (fun w => atomQ m t (1 - w)) (-deriv (atomQ m t) (1 - z)) z := by
      have := (hQd (1 - z)).hasDerivAt.comp z ((hasDerivAt_id z).const_sub 1)
      simpa [Function.comp_def] using this
    have hd : HasDerivAt r ((-deriv (atomQ m t) (1 - z) * atomQ m t z -
        atomQ m t (1 - z) * deriv (atomQ m t) z) / atomQ m t z ^ 2) z :=
      hd1.div (hQd z).hasDerivAt (hne z hz)
    rw [hd.deriv]
    have hq1 := hne z hz
    have hq2 := hne' z hz
    rw [atomicPairSeries_one_sub] at hL2
    have e1 : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
      rw [← hL1]; field_simp
    have e2 : deriv (atomQ m t) (1 - z) =
        -atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t (1 - z) := by
      rw [← hL2]; field_simp
    rw [e1, e2]
    simp only [Pi.zero_apply]
    field_simp
    ring
  have hhalf : (1 / 2 : ℂ) ∈ U := by simp [hU]
  have hconst : ∀ z ∈ U, r z = r (1 / 2) := fun z hz =>
    hUo.is_const_of_deriv_eq_zero hUc.isPreconnected hrd hderiv hz hhalf
  have hr1 : r (1 / 2) = 1 := by
    simp only [hr]
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    exact div_self (hne _ hhalf)
  -- the identity theorem extends `Q(1−z) = Q(z)` from `U` to `ℂ`
  have hA := analyticOnNhd_atomQ hone hsum
  have hA' : AnalyticOnNhd ℂ (fun z => atomQ m t (1 - z)) Set.univ := fun z _ => by
    have := (hA (1 - z) (Set.mem_univ _)).comp (f := fun w : ℂ => 1 - w) (by fun_prop)
    simpa [Function.comp_def] using this
  have hev : (fun z => atomQ m t (1 - z)) =ᶠ[𝓝 (1 / 2)] atomQ m t := by
    filter_upwards [hUo.mem_nhds hhalf] with z hz
    have h := hconst z hz
    rw [hr1] at h
    simp only [hr] at h
    exact (div_eq_one_iff_eq (hne z hz)).mp h
  exact hA'.eqOn_of_preconnected_of_eventuallyEq hA isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ s)

/-! ### The Dirichlet side -/

/-- `lam` on `n ≥ 2`. -/
def lamTwo (lam : ℕ → ℝ) (n : ℕ) : ℂ := if 2 ≤ n then (lam n : ℂ) else 0

/-- `lam(n)/log n` on `n ≥ 2`. -/
def lamLog (lam : ℕ → ℝ) (n : ℕ) : ℂ :=
  if 2 ≤ n then (lam n : ℂ) / (Real.log n : ℂ) else 0

theorem logMul_lamLog (lam : ℕ → ℝ) : LSeries.logMul (lamLog lam) = lamTwo lam := by
  funext n
  simp only [LSeries.logMul, lamLog, lamTwo]
  split_ifs with h
  · have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
    have hlog : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    field_simp
  · simp

theorem lamLog_zero (lam : ℕ → ℝ) : lamLog lam 0 = 0 := by simp [lamLog]
theorem lamLog_one (lam : ℕ → ℝ) : lamLog lam 1 = 0 := by simp [lamLog]

theorem norm_lamTwo_le (lam : ℕ → ℝ) (n : ℕ) : ‖lamTwo lam n‖ ≤ 1 * |lam n| := by
  unfold lamTwo
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  · simp

theorem norm_lamLog_le (lam : ℕ → ℝ) (n : ℕ) : ‖lamLog lam n‖ ≤ 2 * |lam n| := by
  unfold lamLog
  split_ifs with h
  · have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hpos : 0 < Real.log n := by linarith
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith [abs_nonneg (lam n)]
  · simp

theorem lseriesSummable_of_le {f : ℕ → ℂ} {lam : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C * |lam n|)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable f s := by
  refine Summable.of_norm_bounded ((hsl s.re hs).mul_left C) fun n => ?_
  rw [LSeries.term_def]
  split_ifs with h
  · subst h
    rw [norm_zero, Nat.cast_zero, Real.zero_rpow (by linarith), div_zero, mul_zero]
  · have hn : 0 < n := Nat.pos_of_ne_zero h
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hf n) (by positivity)

theorem abscissa_lamLog_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    LSeries.abscissaOfAbsConv (lamLog lam) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    lseriesSummable_of_le (norm_lamLog_le lam) hsl (by simpa using hy)

/-- The Dirichlet series `exp(Σ_{n≥2} lam(n) n^{-s}/log n)`. -/
def zetaOf (lam : ℕ → ℝ) (s : ℂ) : ℂ := Complex.exp (LSeries (lamLog lam) s)

/-- `G(s) = s(s−1)Γ_ℝ(s) exp(Σ lam(n)n^{-s}/log n)`. -/
def bigG (lam : ℕ → ℝ) (s : ℂ) : ℂ := s * (s - 1) * Complex.Gammaℝ s * zetaOf lam s

theorem bigG_ne_zero (lam : ℕ → ℝ) {s : ℂ} (hs : 1 < s.re) : bigG lam s ≠ 0 := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1)
    (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))) (Complex.exp_ne_zero _)

/-- **The logarithmic derivative of `G`.**  On `Re s > 1`,
`G'/G = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ − Σ_{n≥2} lam(n)n^{-s}`. -/
theorem hasDerivAt_bigG {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt (bigG lam) (bigG lam s * (1 / s + 1 / (s - 1) + gammaRealLogConnection s -
      LSeries (lamTwo lam) s)) s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hre : 0 < s.re := by linarith
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have habs : LSeries.abscissaOfAbsConv (lamLog lam) < (s.re : EReal) :=
    lt_of_le_of_lt (abscissa_lamLog_le hsl) (by exact_mod_cast hs)
  have hf : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)
  have hg : HasDerivAt Complex.Gammaℝ (gammaRealLogConnection s * Complex.Gammaℝ s) s := by
    have hd := (differentiableAt_Gammaℝ hre).hasDerivAt
    have hl := logDeriv_Gammaℝ hre
    rw [logDeriv_apply] at hl
    have : deriv Complex.Gammaℝ s = gammaRealLogConnection s * Complex.Gammaℝ s := by
      rw [← hl]; field_simp
    rwa [this] at hd
  have hh : HasDerivAt (zetaOf lam) (zetaOf lam s * (-LSeries (lamTwo lam) s)) s := by
    have hL := LSeries_hasDerivAt habs
    rw [logMul_lamLog] at hL
    exact hL.cexp
  have hprod := (hf.mul hg).mul hh
  refine hprod.congr_deriv ?_
  unfold bigG
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- **`G` is the atom product on `Re s > 1`.**  `G = K Q` with `K = G(2)/Q(2)`. -/
theorem bigG_eq_mul_atomQ {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j) t s)
    {s : ℂ} (hs : 1 < s.re) :
    bigG lam s = (bigG lam 2 / atomQ m t 2) * atomQ m t s := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := convex_halfSpace_re_gt 1
  have hQd := differentiable_atomQ hone hsum
  have hQne : ∀ z ∈ V, atomQ m t z ≠ 0 := fun z hz =>
    atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (by
      have : (1 : ℝ) < z.re := hz; intro h; rw [h] at this; norm_num at this))
  set r : ℂ → ℂ := fun z => bigG lam z / atomQ m t z with hr
  have hrd : DifferentiableOn ℂ r V := fun z hz =>
    ((hasDerivAt_bigG hsl hz).differentiableAt.div (hQd z) (hQne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_re_ne (by
      have : (1 : ℝ) < z.re := hz; intro h; rw [h] at this; norm_num at this)
    have hL := logDeriv_atomQ hone hsum hz1
    rw [logDeriv_apply] at hL
    have hQ' : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
      rw [← hL]; field_simp [hQne z hz]
    have hG := hasDerivAt_bigG hsl (show 1 < z.re from hz)
    have hd : HasDerivAt r ((bigG lam z * (1 / z + 1 / (z - 1) + gammaRealLogConnection z -
        LSeries (lamTwo lam) z) * atomQ m t z - bigG lam z * deriv (atomQ m t) z) /
          atomQ m t z ^ 2) z :=
      hG.div (hQd z).hasDerivAt (hQne z hz)
    rw [hd.deriv, hQ', ← hid z hz]
    have hze : zetaArchimedeanDatum z = 1 / z + gammaRealLogConnection z := by
      unfold zetaArchimedeanDatum gammaRealLogConnection; ring
    rw [hze]
    simp only [Pi.zero_apply]
    ring
  have h2 : (2 : ℂ) ∈ V := by simp [hV]
  have hc := hVo.is_const_of_deriv_eq_zero hVc.isPreconnected hrd hderiv hs h2
  simp only [hr] at hc
  have hQs := hQne s hs
  rw [div_eq_iff hQs] at hc
  rw [hc]

/-! ### The completed function and its growth -/

/-- `K = G(2)/Q(2)`. -/
def bigK (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) : ℂ := bigG lam 2 / atomQ m t 2

/-- The completed function `Ĝ = K Q`: entire, and equal to `G` on `Re s > 1`. -/
def ghat (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ := bigK lam m t * atomQ m t s

theorem analyticOnNhd_ghat {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) :
    AnalyticOnNhd ℂ (ghat lam m t) Set.univ := fun s _ =>
  analyticAt_const.mul (analyticOnNhd_atomQ hone hsum s (Set.mem_univ s))

theorem differentiable_ghat {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) : Differentiable ℂ (ghat lam m t) :=
  fun s => (analyticOnNhd_ghat hone hsum s (Set.mem_univ s)).differentiableAt

theorem ghat_one_sub {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (s : ℂ) :
    ghat lam m t (1 - s) = ghat lam m t s := by
  unfold ghat; rw [atomQ_one_sub hone hsum]

theorem hasDerivAt_ghat {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {z : ℂ}
    (hz : ∀ i : AtomIndex m, z ≠ atomAt t i) :
    HasDerivAt (ghat lam m t)
      (atomicPairSeries (fun j => Real.pi * m j) t z * ghat lam m t z) z := by
  have hQd := differentiable_atomQ hone hsum
  have hL := logDeriv_atomQ hone hsum hz
  rw [logDeriv_apply] at hL
  have hne := atomQ_ne_zero hone hsum hz
  have e : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
    rw [← hL]; field_simp
  have h := ((hQd z).hasDerivAt).const_mul (bigK lam m t)
  rw [e] at h
  have h' : HasDerivAt (ghat lam m t) (bigK lam m t *
      (atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z)) z := h
  refine h'.congr_deriv ?_
  unfold ghat
  ring

/-- `Re(2w/(w² + τ²)) ≥ 0` when `Re w > 0`: it is `Re(1/(w − iτ)) + Re(1/(w + iτ))`. -/
theorem re_two_mul_div_nonneg {w : ℂ} (hw : 0 < w.re) (τ : ℝ) :
    0 ≤ (2 * w / (w ^ 2 + (τ : ℂ) ^ 2)).re := by
  have h1 : w - τ * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : w + τ * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hprod : w ^ 2 + (τ : ℂ) ^ 2 = (w - τ * I) * (w + τ * I) := by
    ring_nf; rw [I_sq]; ring
  have e : 2 * w / (w ^ 2 + (τ : ℂ) ^ 2) = (w - τ * I)⁻¹ + (w + τ * I)⁻¹ := by
    rw [hprod]; field_simp; ring
  rw [e, Complex.add_re, Complex.inv_re, Complex.inv_re]
  have r1 : (w - τ * I).re = w.re := by simp
  have r2 : (w + τ * I).re = w.re := by simp
  rw [r1, r2]
  exact add_nonneg (div_nonneg hw.le (Complex.normSq_nonneg _))
    (div_nonneg hw.le (Complex.normSq_nonneg _))

/-- **Positivity of the atomic Herglotz series** on `Re z > ½`. -/
theorem re_atomicPairSeries_nonneg (m : ℕ → ℕ) (t : ℕ → ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    0 ≤ (atomicPairSeries (fun j => Real.pi * m j) t z).re := by
  unfold atomicPairSeries
  rw [← tsum_mul_left]
  set w := z - 1 / 2 with hw
  have hwre : 0 < w.re := by simp [hw]; linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm : ∀ j, 0 ≤ (2 * w / (Real.pi : ℂ) *
      (((Real.pi * m j : ℝ) : ℂ) / (w ^ 2 + (t j : ℂ) ^ 2))).re := by
    intro j
    have e : 2 * w / (Real.pi : ℂ) * (((Real.pi * m j : ℝ) : ℂ) / (w ^ 2 + (t j : ℂ) ^ 2)) =
        ((m j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
      push_cast; field_simp
    rw [e, Complex.re_ofReal_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (re_two_mul_div_nonneg hwre (t j))
  by_cases hS : Summable fun j => 2 * w / (Real.pi : ℂ) *
      (((Real.pi * m j : ℝ) : ℂ) / (w ^ 2 + (t j : ℂ) ^ 2))
  · rw [Complex.re_tsum hS]; exact tsum_nonneg hterm
  · rw [tsum_eq_zero_of_not_summable hS]; simp

/-- **Horizontal monotonicity.**  `|Ĝ(σ + iτ)| ≤ |Ĝ(2 + iτ)|` for `½ ≤ σ ≤ 2`. -/
theorem norm_ghat_le_two {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) {σ : ℝ} (τ : ℝ) (h1 : 1 / 2 ≤ σ)
    (h2 : σ ≤ 2) : ‖ghat lam m t (σ + τ * I)‖ ≤ ‖ghat lam m t (2 + τ * I)‖ := by
  set φ : ℝ → ℝ := fun x => ‖ghat lam m t (x + τ * I)‖ ^ 2 with hφ
  have hgd := differentiable_ghat (lam := lam) hone hsum
  have hcont : Continuous φ :=
    ((hgd.continuous.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + τ * I)).norm).pow 2
  have hderiv : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt φ
      (2 * inner ℝ (ghat lam m t (x + τ * I))
        (atomicPairSeries (fun j => Real.pi * m j) t (x + τ * I) * ghat lam m t (x + τ * I))) x := by
    intro x hx
    have hre : ((x : ℂ) + τ * I).re ≠ 1 / 2 := by
      simp; linarith [hx.1]
    have hd := hasDerivAt_ghat (lam := lam) hone hsum (ne_atomAt_of_re_ne (m := m) (t := t) hre)
    have hd2 : HasDerivAt (fun y : ℂ => ghat lam m t (y + τ * I))
        (atomicPairSeries (fun j => Real.pi * m j) t (x + τ * I) * ghat lam m t (x + τ * I))
        (x : ℂ) := hd.comp_add_const _ _
    exact hd2.comp_ofReal.norm_sq
  have hnonneg : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2, 0 ≤ 2 * inner ℝ (ghat lam m t (x + τ * I))
      (atomicPairSeries (fun j => Real.pi * m j) t (x + τ * I) * ghat lam m t (x + τ * I)) := by
    intro x hx
    rw [Complex.inner]
    set g := ghat lam m t (x + τ * I)
    set Φ := atomicPairSeries (fun j => Real.pi * m j) t (x + τ * I)
    have e : Φ * g * (starRingEnd ℂ) g = ((Complex.normSq g : ℝ) : ℂ) * Φ := by
      rw [mul_assoc, Complex.mul_conj]; ring
    rw [e, Complex.re_ofReal_mul]
    have hre : 1 / 2 < ((x : ℂ) + τ * I).re := by simp; linarith [hx.1]
    exact mul_nonneg (by norm_num) (mul_nonneg (Complex.normSq_nonneg _)
      (re_atomicPairSeries_nonneg m t hre))
  have hmono : MonotoneOn φ (Set.Icc (1 / 2) 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      exact hnonneg x hx
  have h := hmono ⟨h1, h2⟩ ⟨by norm_num, le_rfl⟩ h2
  simp only [hφ] at h
  push_cast at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Stirling on `Re s = 2`: `|Γ_ℝ(2 + iτ)| ≤ C (|τ| + 4)^N e^{−π|τ|/4}`. -/
theorem exists_bound_Gammaℝ_two :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖Complex.Gammaℝ (2 + τ * I)‖ ≤ C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  obtain ⟨Cs, N, hCs, hs⟩ := exists_sharp_bound_norm_Gamma_strip 1 1
  have hcont : Continuous fun τ : ℝ => Complex.Gamma (1 + (τ / 2 : ℝ) * I) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    refine ContinuousAt.comp (g := Complex.Gamma) (f := fun τ : ℝ => 1 + ((τ / 2 : ℝ) : ℂ) * I)
      (Complex.continuousAt_Gamma _ fun m hm => ?_) (by fun_prop)
    have h := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp at h
    linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  set C₀ : ℝ := max Cs (max B 0 * Real.exp (Real.pi / 2)) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_trans hCs (le_max_left _ _)
  refine ⟨C₀, N, hC₀0, fun τ => ?_⟩
  have hpi := Real.pi_pos
  have hΓℝ : Complex.Gammaℝ (2 + τ * I) =
      (Real.pi : ℂ) ^ (-(2 + τ * I) / 2) * Complex.Gamma (1 + (τ / 2 : ℝ) * I) := by
    rw [Complex.Gammaℝ_def]
    congr 2
    push_cast; ring
  have hπ : ‖(Real.pi : ℂ) ^ (-(2 + τ * I) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have hre : (-(2 + (τ : ℂ) * I) / 2).re = -1 := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hτ := abs_nonneg τ
  have hpow1 : (1 : ℝ) ≤ (|τ| + 4) ^ N := one_le_pow₀ (by linarith)
  have key : ‖Complex.Gamma (1 + (τ / 2 : ℝ) * I)‖ ≤
      C₀ * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
    rcases le_or_gt 2 |τ| with h1 | h1
    · have him : (1 + ((τ / 2 : ℝ) : ℂ) * I).im = τ / 2 := by simp
      have hre : (1 + ((τ / 2 : ℝ) : ℂ) * I).re = 1 := by simp
      have h := hs (1 + ((τ / 2 : ℝ) : ℂ) * I) (by rw [hre]) (by rw [hre])
        (by rw [him, abs_div, abs_two]; linarith)
      rw [him, abs_div, abs_two] at h
      have hexp : Real.exp (-(Real.pi * (|τ| / 2) / 2)) = Real.exp (-(Real.pi * |τ| / 4)) := by
        congr 1; ring
      rw [hexp] at h
      calc ‖Complex.Gamma (1 + ((τ / 2 : ℝ) : ℂ) * I)‖
          ≤ Cs * (|τ| / 2) ^ N * Real.exp (-(Real.pi * |τ| / 4)) := h
        _ ≤ C₀ * (|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4)) := by
            gcongr
            · exact le_max_left _ _
            · linarith
        _ = _ := by ring
    · have hmem : τ ∈ Set.Icc (-2 : ℝ) 2 := by
        rw [abs_lt] at h1; exact ⟨h1.1.le, h1.2.le⟩
      have hb := (hB τ hmem).trans (le_max_left B 0)
      have hexp : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi * |τ| / 4)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      have hB0 : 0 ≤ max B 0 := le_max_right _ _
      calc ‖Complex.Gamma (1 + ((τ / 2 : ℝ) : ℂ) * I)‖ ≤ max B 0 := hb
        _ = max B 0 * Real.exp (Real.pi / 2) * 1 * Real.exp (-(Real.pi / 2)) := by
            rw [mul_one, mul_assoc, ← Real.exp_add]; simp
        _ ≤ C₀ * (|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4)) :=
            mul_le_mul (mul_le_mul (le_max_right _ _) hpow1 zero_le_one hC₀0) hexp
              (by positivity) (by positivity)
        _ = _ := by ring
  rw [hΓℝ, norm_mul]
  calc ‖(Real.pi : ℂ) ^ (-(2 + τ * I) / 2)‖ * ‖Complex.Gamma (1 + ((τ / 2 : ℝ) : ℂ) * I)‖
      ≤ 1 * (C₀ * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4)))) :=
        mul_le_mul hπ key (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Growth on `Re s = 2`.**  `|Ĝ(2 + iτ)| ≤ C (|τ| + 4)^N e^{−π|τ|/4}`. -/
theorem exists_bound_ghat_two {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j) t s) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖ghat lam m t (2 + τ * I)‖ ≤ C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := exists_bound_Gammaℝ_two
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) 2 n‖ with hS
  refine ⟨Cγ * Real.exp S, Nγ + 2, by positivity, fun τ => ?_⟩
  have hre : (1 : ℝ) < (2 + (τ : ℂ) * I).re := by simp
  rw [show ghat lam m t (2 + τ * I) = bigG lam (2 + τ * I) from
    (bigG_eq_mul_atomQ hone hsum hsl hid hre).symm]
  unfold bigG zetaOf
  have hsumm : LSeriesSummable (lamLog lam) (2 + τ * I) :=
    lseriesSummable_of_le (norm_lamLog_le lam) hsl hre
  have hL : ‖LSeries (lamLog lam) (2 + τ * I)‖ ≤ S := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsumm.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hz : ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖ ≤ Real.exp S := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  have hτ := abs_nonneg τ
  have h1 : ‖(2 + (τ : ℂ) * I)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I)‖ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have h2 : ‖(2 + (τ : ℂ) * I - 1)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I - 1)‖ = ‖(1 : ℂ) + (τ : ℂ) * I‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have hE : 0 ≤ (|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)) := by positivity
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(2 + (τ : ℂ) * I)‖ * ‖(2 + (τ : ℂ) * I - 1)‖ * ‖Complex.Gammaℝ (2 + τ * I)‖ *
        ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖
      ≤ (|τ| + 4) * (|τ| + 4) * (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) *
          Real.exp S := by
        gcongr
        exact hγ τ
    _ = Cγ * Real.exp S * ((|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4))) := by ring

/-! ### The removable singularity at `s = 1` -/

/-- `s(s−1)Γ_ℝ(s−1) = 2s π^{−(s−1)/2} Γ((s−1)/2 + 1)`, holomorphic on `Re s > −1`. -/
def mFactor (s : ℂ) : ℂ := 2 * s * ((Real.pi : ℂ) ^ (-(s - 1) / 2) * Complex.Gamma ((s - 1) / 2 + 1))

theorem mFactor_eq {s : ℂ} (h1 : s ≠ 1) : mFactor s = s * (s - 1) * Complex.Gammaℝ (s - 1) := by
  unfold mFactor
  rw [mul_assoc s, sub_one_mul_Gammaℝ_sub_one h1]
  ring

theorem mFactor_one : mFactor 1 = 2 := by
  simp [mFactor]

theorem differentiableAt_mFactor {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ mFactor s := by
  unfold mFactor
  have hΓ : DifferentiableAt ℂ Complex.Gamma ((s - 1) / 2 + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this
    linarith
  refine DifferentiableAt.mul (by fun_prop) (DifferentiableAt.mul ?_ (hΓ.comp s (by fun_prop)))
  exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))

/-- `β = Ĝ(1)/2`. -/
def betaK (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) : ℂ := ghat lam m t 1 / 2

/-- `Ĝ − β · s(s−1)Γ_ℝ(s−1)`, which vanishes at `s = 1`. -/
def numN (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ :=
  ghat lam m t s - betaK lam m t * mFactor s

/-- `E(s) = Ĝ(s)/(s(s−1)) − β Γ_ℝ(s−1)`, continued across `s = 1`. -/
def bigE (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ :=
  dslope (numN lam m t) 1 s / s

theorem numN_one (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) : numN lam m t 1 = 0 := by
  unfold numN betaK; rw [mFactor_one]; ring

theorem bigE_eq (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    bigE lam m t s = ghat lam m t s / (s * (s - 1)) - betaK lam m t * Complex.Gammaℝ (s - 1) := by
  unfold bigE
  rw [dslope_of_ne _ h1, slope_def_module, numN_one, sub_zero, smul_eq_mul]
  unfold numN
  rw [mFactor_eq h1]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

theorem differentiableOn_bigE {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) :
    DifferentiableOn ℂ (bigE lam m t) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hN : DifferentiableOn ℂ (numN lam m t) {s : ℂ | 0 < s.re} := fun s hs =>
    ((differentiable_ghat hone hsum s).sub
      ((differentiableAt_mFactor hs).const_mul _)).differentiableWithinAt
  have hD : DifferentiableOn ℂ (dslope (numN lam m t) 1) {s : ℂ | 0 < s.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds (by norm_num))).mpr hN
  intro s hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  exact ((hD s hs).differentiableAt (hopen.mem_nhds hs)).div differentiableAt_id hs0
    |>.differentiableWithinAt

/-- **Decay of `E`** on the closed strip `½ ≤ Re s ≤ 3/2`. -/
theorem exists_decay_bigE {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j) t s) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖bigE lam m t s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := exists_bound_ghat_two hone hsum hsl hid
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_pow_mul_exp_neg (N₁ + 2)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (bigE lam m t) (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) :=
    (differentiableOn_bigE hone hsum).continuousOn.mono fun z hz => by
      rw [Complex.mem_reProdIm] at hz
      show 0 < z.re
      linarith [hz.1.1]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  set β := betaK lam m t with hβ
  refine ⟨max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0), fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  set τ := s.im with hτ
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  rcases le_or_gt 4 |τ| with h4 | h4
  · have hn1 : 4 ≤ ‖s‖ := h4.trans (Complex.abs_im_le_norm s)
    have hn2 : 4 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have h0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hn1; norm_num at hn1
    have h1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn2; norm_num at hn2
    rw [bigE_eq lam m t h0 h1]
    have hs_eq : (s.re : ℂ) + τ * I = s := Complex.re_add_im s
    have hg : ‖ghat lam m t s‖ ≤ C₁ * ((|τ| + 4) ^ N₁ * Real.exp (-(Real.pi * |τ| / 4))) := by
      rw [← hs_eq]
      exact (norm_ghat_le_two hone hsum τ hs.1 (by linarith [hs.2])).trans (h₁ τ)
    have hdec := pow_mul_exp_neg_le_div hK₁ (abs_nonneg τ)
    rw [sq_abs] at hdec
    have hden : 1 ≤ ‖s * (s - 1)‖ := by
      rw [norm_mul]; nlinarith
    have hΓ := h₃ s hs.1 hs.2 h4
    calc ‖ghat lam m t s / (s * (s - 1)) - β * Complex.Gammaℝ (s - 1)‖
        ≤ ‖ghat lam m t s / (s * (s - 1))‖ + ‖β‖ * ‖Complex.Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖ghat lam m t s‖ + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          rw [norm_div]
          exact div_le_self (norm_nonneg _) hden
      _ ≤ C₁ * (K₁ / (1 + τ ^ 2)) + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          exact hg.trans (mul_le_mul_of_nonneg_left hdec hC₁)
      _ = (C₁ * K₁ + ‖β‖ * C₃) / (1 + τ ^ 2) := by ring
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_left _ _
  · have hab := abs_lt.mp h4
    have hmem : s ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 := by
      rw [Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, ⟨hab.1.le, hab.2.le⟩⟩
    have hb := (hB s hmem).trans (le_max_left B 0)
    have hτ2 : τ ^ 2 ≤ 16 := by nlinarith
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    calc ‖bigE lam m t s‖ ≤ max B 0 := hb
      _ ≤ 17 * max B 0 / (1 + τ ^ 2) := by
          rw [le_div_iff₀ hpos]; nlinarith
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_right _ _

theorem hasDerivAt_zetaOf {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt (zetaOf lam) (zetaOf lam s * (-LSeries (lamTwo lam) s)) s := by
  have habs : LSeries.abscissaOfAbsConv (lamLog lam) < (s.re : EReal) :=
    lt_of_le_of_lt (abscissa_lamLog_le hsl) (by exact_mod_cast hs)
  have hL := LSeries_hasDerivAt habs
  rw [logMul_lamLog] at hL
  exact hL.cexp

/-! ### Integer spectral masses force `Λ` and RH -/

/-- **Integer spectral masses force `Λ` and the Riemann hypothesis.**  Let
`Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and let integer masses `m_j` at ordinates `t_j ≥ 1`
(`Σ m_j/t_j² < ∞`) represent the Weil function on `Re s > 1`:
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)`.
Then `lam(n) = Λ(n)` for `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem integer_mass_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hid' : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j) t s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigE hone hsum hsl hid'
  have hdE := differentiableOn_bigE (lam := lam) hone hsum
  set β := betaK lam m t with hβ
  have hcoef := HamburgerStability.coeff_eq_of_critical_line_even_sublinear_defect
    (a := a) ha (E := bigE lam m t) (β := β) (C := C) (g := fun _ => (0 : ℂ)) (Cg := 0) (N := 0)
    (hdE.continuousOn.mono fun z hz => by
      rw [mem_verticalStrip] at hz; show 0 < z.re; linarith [hz.1])
    (hdE.mono fun z hz => by show 0 < z.re; linarith [hz.1])
    hC
    (fun s hs => by
      have h1 : 1 < s.re := by rw [hs]; norm_num
      have h0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [coeffDirichlet_eq_LSeries, (hLa s h1).2, bigE_eq lam m t h0 hs1,
        show ghat lam m t s = bigG lam s from (bigG_eq_mul_atomQ hone hsum hsl hid' h1).symm]
      unfold bigG
      field_simp
      ring)
    (fun s hs => by
      have h0 : s ≠ 0 := ne_zero_of_re_eq_half hs
      have hs1 : s ≠ 1 := ne_one_of_re_eq_half hs
      have hre' : (1 - s).re = 1 / 2 := by simp [hs]; norm_num
      have h0' : 1 - s ≠ 0 := ne_zero_of_re_eq_half hre'
      have h1' : 1 - s ≠ 1 := ne_one_of_re_eq_half hre'
      rw [bigE_eq lam m t h0 hs1, bigE_eq lam m t h0' h1', ghat_one_sub hone hsum]
      have hden : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
      rw [hden, show (1 : ℂ) - s - 1 = -s by ring]
      ring)
    measurable_const (fun _ => by simp) (by simp)
  -- all coefficients equal `a 1 = 1`
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have h2β : 2 * β = 1 := by rw [← hcoef 0, ha1]
  have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hcoef k, h2β]; rfl
  have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
    intro s hs
    rw [← (hLa s hs).2, LSeries_congr hall s, LSeries_one_eq_riemannZeta hs]
  -- `lam = Λ` on `n ≥ 2`
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hζ z hz).symm
    have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
    have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
    field_simp
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  -- the Riemann hypothesis
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    set Z : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1 with hZ
    have hZd : Differentiable ℂ Z := by
      have := differentiable_completedZeta₀
      intro s; simp only [hZ]; fun_prop
    have hZa : AnalyticOnNhd ℂ Z Set.univ :=
      hZd.differentiableOn.analyticOnNhd isOpen_univ
    have hZΛ : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Z s = s * (s - 1) * completedRiemannZeta s := by
      intro s h0 h1
      have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      simp only [hZ]
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    have hΛζ : ∀ s : ℂ, 0 < s.re → completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      intro s hs
      have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
      rw [riemannZeta_def_of_ne_zero h0]
      field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : ghat lam m t =ᶠ[𝓝 (2 : ℂ)] Z := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [hZΛ z h0 h1, hΛζ z (by linarith), ← hζ z hz',
        show ghat lam m t z = bigG lam z from (bigG_eq_mul_atomQ hone hsum hsl hid' hz').symm]
      unfold bigG; ring
    have hglob := (analyticOnNhd_ghat (lam := lam) hone hsum).eqOn_of_preconnected_of_eventuallyEq
      hZa isPreconnected_univ (Set.mem_univ _) hev (Set.mem_univ ρ)
    have hρne0 : ρ ≠ 0 := by intro h; rw [h] at hρ1; simp at hρ1; linarith
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : ghat lam m t ρ = 0 := by
      rw [hglob, hZΛ ρ hρne0 hρne1, hΛζ ρ (by linarith), hρ0, mul_zero, mul_zero]
    have hK : bigK lam m t ≠ 0 := by
      unfold bigK
      refine div_ne_zero (bigG_ne_zero lam (by norm_num)) (atomQ_ne_zero hone hsum ?_)
      exact ne_atomAt_of_re_ne (by norm_num)
    have hQ : atomQ m t ρ ≠ 0 :=
      atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (by intro h; linarith))
    exact mul_ne_zero hK hQ hzero

end

end IntegerMassRigidity

end RHTower
