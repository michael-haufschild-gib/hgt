import GaloisForLFunctions.TensorPowerProgramme.ThePrimeNumberTheoremOfTheCharactersGivesTheirIndependence
import GaloisForLFunctions.TensorPowerProgramme.TheEulerLogarithmDifferentiatesToThePrimePowerSeries
import GaloisForLFunctions.FamilyContinuationTheory.GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip
import GaloisForLFunctions.TensorPowerProgramme.TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne

/-!
# The angles of the Eisenstein field are an abelian base

Over `K = ℚ(ω)` the sextic Grossencharacter `ψ₆` gives each prime ideal `v` an angle
`ψ₆(v)` on the unit circle. The **angle base** has the prime powers `v^{m+1}` as points, norm
`N(v)^{m+1}`, weight `log N(v)`, and characters `j ∈ ℤ` acting by `ψ₆(v)^{j(m+1)}`. Its
prime-number-theorem series are logarithmic derivatives of `L`-functions over `K`
(`baseLSeries_angle`):

* `j = 0`: `−ζ_K'/ζ_K` with `ζ_K = ζ · L(χ₋₃)`, a simple pole of residue one at `s = 1`;
* `j ≥ 1`: `−L'/L(ψ₆^j)`, continuous on `Re s ≥ 1` (holomorphic on `Re s > −3j`, nonvanishing on
  `Re s ≥ 1`);
* `j ≤ −1`: the complex conjugate of the case `−j` at `conj s`.

So the angle characters form an abelian base (`isAbelianBase_angle`), and every flow datum over
the angle base is a ruler: its `k`-th tensor moment converges exactly for `σ > 1 + 2kW`
(`summable_angleMomentTerm_iff`). The angles enter the moments only through the base, with base
loss exactly one.
-/

open Complex Filter Topology
open NumberField IsDedekindDomain
open GaloisForLFunctions.FamilyContinuationTheory GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
open GaloisForLFunctions.HeckeLFunctions MetaplecticMobiusDescent.Eisenstein

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- Points of the angle base: `(v, m)` stands for the prime power `v^{m+1}`. -/
abbrev AnglePoint := HeightOneSpectrum O × ℕ

/-- The norm `N(v)^{m+1}` of the point `(v, m)`. -/
def angleNorm (x : AnglePoint) : ℝ := ((x.1.asIdeal.absNorm ^ (x.2 + 1) : ℕ) : ℝ)

/-- The weight `log N(v)` of the point `(v, m)`. -/
def angleLam (x : AnglePoint) : ℝ := Real.log x.1.asIdeal.absNorm

/-- The character `j` at `(v, m)`: the angle `ψ₆(v)^{j(m+1)}`. -/
def angleEv (j : Multiplicative ℤ) (x : AnglePoint) : ℂ :=
  idealPsiSix x.1.asIdeal ^ (Multiplicative.toAdd j * ((x.2 : ℤ) + 1))

/-- The Euler coefficient `ψ₆(v)^j` of the character `j`. -/
def angleCoeff (j : ℤ) (v : HeightOneSpectrum O) : ℂ := idealPsiSix v.asIdeal ^ j

theorem idealPsiSix_prime_ne_zero (v : HeightOneSpectrum O) : idealPsiSix v.asIdeal ≠ 0 := by
  intro h
  have := norm_idealPsiSix_prime v
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem norm_angleCoeff (j : ℤ) (v : HeightOneSpectrum O) : ‖angleCoeff j v‖ = 1 := by
  rw [angleCoeff, norm_zpow, norm_idealPsiSix_prime, one_zpow]

/-- `(a^n)^s = (a^s)^n` for a natural number `a`. -/
theorem natCast_pow_cpow (a n : ℕ) (s : ℂ) :
    (((a ^ n : ℕ) : ℂ)) ^ s = ((a : ℂ) ^ s) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- The prime-number-theorem series of the character `j` is the prime-power series of `ψ₆^j`. -/
theorem baseLSeries_angle (j : Multiplicative ℤ) (s : ℂ) :
    baseLSeries angleNorm angleLam angleEv j s =
      primePowerSeries (angleCoeff (Multiplicative.toAdd j)) s := by
  rw [baseLSeries, primePowerSeries]
  refine tsum_congr fun x => ?_
  rw [angleNorm, angleLam, angleEv, eulerRatio, angleCoeff, Complex.ofReal_natCast,
    natCast_pow_cpow, mul_pow, ← zpow_natCast, ← zpow_mul, mul_assoc]
  push_cast
  ring_nf

/-! ### The prime number theorem of each character -/

/-- At the trivial modulus the primitive character of `1` is `1` at every prime. -/
theorem primitiveIdealValue_trivial_prime (v : HeightOneSpectrum O) :
    primitiveIdealValue (trivialModulus K) 1 v.asIdeal = 1 := by
  have hv : ¬ ((trivialModulus K).fin ≤ v.asIdeal) := by
    intro h
    apply v.isPrime.ne_top
    rw [eq_top_iff]
    exact le_trans (by simp [trivialModulus]) h
  rw [primitiveIdealValue_eq_heckeValue_of_not_le _ _ hv]
  exact heckeValue_trivialModulus_one v.ne_bot

/-- For `k ≥ 1`, `ψ₆^k` is the Euler product of the Grossencharacter `L`-function. -/
theorem exp_eulerLog_angle {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction (trivialModulus K) 1 k w = Complex.exp (eulerLog (angleCoeff k) w) := by
  rw [← exp_tsum_grossenEulerLog (trivialModulus K) 1 hk hw, eulerLog]
  congr 1
  refine tsum_congr fun v => ?_
  rw [grossenPrimeTerm, primitiveIdealValue_trivial_prime, mul_one, eulerRatio, angleCoeff,
    zpow_natCast]

/-- **The prime number theorem of `ψ₆^k`, `k ≥ 1`.** -/
theorem angle_pnt_pos {k : ℕ} (hk : 1 ≤ k) :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      primePowerSeries (angleCoeff k) s = G s := by
  set Lk := grossenLFunction (trivialModulus K) 1 k
  have hU : IsOpen {w : ℂ | -(3 * (k : ℝ)) < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Lk {w : ℂ | -(3 * (k : ℝ)) < w.re} :=
    differentiableOn_grossenLFunction (trivialModulus K) 1 hk
  have hsub : {s : ℂ | 1 ≤ s.re} ⊆ {w : ℂ | -(3 * (k : ℝ)) < w.re} := fun s hs => by
    simp only [Set.mem_setOf_eq] at hs ⊢
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine ⟨fun s => -deriv Lk s / Lk s, ?_, fun s hs => ?_⟩
  · exact ((hd.deriv hU).continuousOn.mono hsub).neg.div (hd.continuousOn.mono hsub)
      fun s hs => grossenLFunction_ne_zero_of_one_le_re (trivialModulus K) 1 hk hs
  · exact (neg_deriv_div_eq_primePowerSeries (fun v => (norm_angleCoeff k v).le)
      (fun z hz => exp_eulerLog_angle hk hz) hs).symm

/-- Conjugation exchanges `ψ₆^k` and `ψ₆^{−k}`: the series of `−k` is the conjugate of the series
of `k` at `conj s`. -/
theorem primePowerSeries_angle_neg (k : ℕ) (s : ℂ) :
    primePowerSeries (angleCoeff (-(k : ℤ))) s =
      conj (primePowerSeries (angleCoeff k) (conj s)) := by
  rw [primePowerSeries, primePowerSeries, Complex.conj_tsum]
  refine tsum_congr fun x => ?_
  have hpos : (0 : ℝ) < x.1.asIdeal.absNorm := by
    exact_mod_cast lt_of_lt_of_le two_pos (two_le_absNorm_prime x.1)
  have h1 : angleCoeff (-(k : ℤ)) x.1 = conj (angleCoeff k x.1) := by
    rw [← Complex.inv_eq_conj (norm_angleCoeff _ _), angleCoeff, angleCoeff, zpow_neg]
  have h2 : ((x.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-s) =
      conj (((x.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-conj s)) := by
    rw [← Complex.ofReal_natCast, conj_ofReal_cpow hpos, map_neg, Complex.conj_conj]
  simp only [eulerRatio, map_mul, map_pow, Complex.conj_ofReal]
  rw [h1, h2]

/-- **The prime number theorem of `ψ₆^{−k}`, `k ≥ 1`.** -/
theorem angle_pnt_neg {k : ℕ} (hk : 1 ≤ k) :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      primePowerSeries (angleCoeff (-(k : ℤ))) s = G s := by
  obtain ⟨G, hG, hF⟩ := angle_pnt_pos hk
  refine ⟨fun s => conj (G (conj s)), ?_, fun s hs => ?_⟩
  · exact Complex.continuous_conj.comp_continuousOn
      (hG.comp Complex.continuous_conj.continuousOn fun s hs => by simpa using hs)
  · rw [primePowerSeries_angle_neg, hF (conj s) (by simpa using hs)]

/-- The trivial character: `ζ(s) L(s, χ₋₃) = ζ_K(s)` is the Euler product of the angle base. -/
theorem exp_eulerLog_angle_zero {w : ℂ} (hw : 1 < w.re) :
    riemannZeta w * DirichletCharacter.LFunction chi3D w =
      Complex.exp (eulerLog (angleCoeff 0) w) := by
  have hcoef : ∀ v : HeightOneSpectrum O,
      eulerRatio (angleCoeff 0) w v = heckePrimeTerm (trivialModulus K) 1 w v := fun v => by
    rw [eulerRatio, heckePrimeTerm, angleCoeff, zpow_zero, heckeValue_trivialModulus_one v.ne_bot]
  have hsum : Summable fun v : HeightOneSpectrum O =>
      -Complex.log (1 - heckePrimeTerm (trivialModulus K) 1 w v) :=
    (summable_norm_heckePrimeTerm (trivialModulus K) 1 hw).of_norm.clog_one_sub.neg
  have hne : ∀ v, 1 - heckePrimeTerm (trivialModulus K) 1 w v ≠ 0 := fun v h0 => by
    have hlt := norm_heckePrimeTerm_lt_one (trivialModulus K) 1 hw v
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  have h := hsum.hasSum.cexp
  simp only [Function.comp_def, Complex.exp_neg, Complex.exp_log (hne _)] at h
  rw [← dedekindZeta_thirdCyclotomic K hw, ← heckeL_trivialModulus_one, eulerLog]
  simp only [hcoef]
  exact (h.unique (heckeL_eulerProduct_hasProd (trivialModulus K) 1 hw)).symm

theorem neg_div_mul_aux {a b A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    -(a * B + A * b) / (A * B) = -a / A + -b / B := by
  rw [div_add_div _ _ hA hB]
  ring

/-- **The prime number theorem of the trivial angle**: `−ζ_K'/ζ_K = 1/(s − 1) + G`, with
`G = (L(Λ, s) − 1/(s − 1)) − L'/L(χ₋₃)` continuous on `Re s ≥ 1`. -/
theorem angle_pnt_zero :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      primePowerSeries (angleCoeff 0) s = G s + 1 / (s - 1) := by
  refine ⟨fun s => vonMangoldtRegular s + -deriv (DirichletCharacter.LFunction chi3D) s /
    DirichletCharacter.LFunction chi3D s, ?_, fun s hs => ?_⟩
  · refine continuousOn_vonMangoldtRegular.add ?_
    exact (DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv chi3D_ne_one).mono
      fun s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (.inl chi3D_ne_one) hs
  · have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have hχ : DirichletCharacter.LFunction chi3D s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (.inl chi3D_ne_one) hs.le
    have hE := neg_deriv_div_eq_primePowerSeries (fun v => (norm_angleCoeff 0 v).le)
      (L := fun z => riemannZeta z * DirichletCharacter.LFunction chi3D z)
      (fun z hz => exp_eulerLog_angle_zero hz) hs
    rw [← hE, deriv_mul (differentiableAt_riemannZeta hs1)
      ((DirichletCharacter.differentiable_LFunction chi3D_ne_one) s)]
    have hΛ := LSeries_vonMangoldt_eq_regular_add hs
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hΛ
    beta_reduce
    rw [neg_div_mul_aux hζ hχ, hΛ]
    ring

/-! ### The angle base -/

theorem summable_angleLam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : AnglePoint => angleLam x * angleNorm x ^ (-σ) := by
  refine (summable_log_mul_rpow_pow (K := K) hσ).congr fun x => ?_
  have ha : (0 : ℝ) ≤ x.1.asIdeal.absNorm := Nat.cast_nonneg _
  rw [angleLam, angleNorm, Nat.cast_pow, ← Real.rpow_natCast_mul ha,
    show ((x.2 + 1 : ℕ) : ℝ) * -σ = -σ * ((x.2 + 1 : ℕ) : ℝ) from mul_comm _ _,
    Real.rpow_mul_natCast ha]

theorem toAdd_ne_zero_of_ne_one {j : Multiplicative ℤ} (hj : j ≠ 1) : Multiplicative.toAdd j ≠ 0 :=
  fun h => hj (by rw [← ofAdd_toAdd j, h, ofAdd_zero])

/-- **The angle characters of the Eisenstein field form an abelian base.** -/
theorem isAbelianBase_angle : IsAbelianBase angleNorm angleLam angleEv := by
  refine IsAbelianBase.of_pnt (fun x => ?_) (fun x => ?_) (fun σ hσ => summable_angleLam hσ)
    (fun j x => ?_) (fun j j' x => ?_) (fun j x => ?_) ?_ (fun j hj => ?_)
  · have h2 := two_le_absNorm_prime x.1
    exact Nat.one_le_cast.mpr (Nat.one_le_pow _ _ (by omega))
  · exact Real.log_nonneg (Nat.one_le_cast.mpr (by linarith [two_le_absNorm_prime x.1]))
  · rw [angleEv, norm_zpow, norm_idealPsiSix_prime, one_zpow]
  · rw [angleEv, angleEv, angleEv, toAdd_mul, add_mul, zpow_add₀ (idealPsiSix_prime_ne_zero _)]
  · rw [angleEv, angleEv, toAdd_inv, neg_mul, zpow_neg, map_zpow₀,
      ← Complex.inv_eq_conj (norm_idealPsiSix_prime _), inv_zpow]
  · obtain ⟨G, hG, hF⟩ := angle_pnt_zero
    exact ⟨G, hG, fun s hs => by rw [baseLSeries_angle, toAdd_one]; exact hF s hs⟩
  · have h0 := toAdd_ne_zero_of_ne_one hj
    simp_rw [baseLSeries_angle]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, Multiplicative.toAdd j = -(k : ℤ) :=
        ⟨(-Multiplicative.toAdd j).toNat, by omega⟩
      rw [hk]
      exact angle_pnt_neg (k := k) (by omega)
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, Multiplicative.toAdd j = k :=
        ⟨(Multiplicative.toAdd j).toNat, by omega⟩
      rw [hk]
      exact angle_pnt_pos (by omega)

/-- **The angle base is a ruler.** A flow datum over the prime powers of `ℚ(ω)` twisted by angle
characters, with distinct pairs `(z_i, j_i)` and width `W`, has `k`-th tensor moment
`Σ log N(v) |Σ_i b_i ψ₆(v)^{j_i(m+1)} N(v)^{(m+1) z_i}|^{2k} N(v)^{−(m+1)σ}` converging exactly for
`σ > 1 + 2kW`. -/
theorem summable_angleMomentTerm_iff {ι : Type*} [Fintype ι] {z b : ι → ℂ}
    {χ : ι → Multiplicative ℤ} {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → χ i = χ j → i = j) {k : ℕ} (hk : 1 ≤ k)
    (σ : ℝ) :
    Summable (twistMomentTerm angleNorm angleLam angleEv z b χ k σ) ↔ 1 + 2 * k * W < σ :=
  summable_twistMomentTerm_iff isAbelianBase_angle hW hWa hinj hk σ

end GaloisForLFunctions.TensorPowerProgramme
