import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

/-!
# The parity grading of the half-dilated Born partition function

On the temperature strip `0 < β < 2` the half-dilated completed partition function
`Z(β) = Λ(β/2)` is a strictly negative real.  This module realizes the sign by an exact
positive factorization.  The parity grading `n ↦ (-1)^{n-1}` — the unique prime-deletion
grading with unimodular coefficients, and the range-projection grading of the `2`-isometry —
groups the integer levels of the `log √n` Hamiltonian into doublets `{2n+1, 2n+2}`, whose
graded supertrace `∑ ((2n+1)^{-β/2} - (2n+2)^{-β/2})` converges absolutely and is strictly
positive on the whole strip.  The archimedean factor is an ungraded strictly positive real
there.  The completed partition function is recovered through the eta coupling scalar
`1 - 2^{1-β/2}`:

`Γℝ(β/2) · (graded supertrace) = (eta coupling) · Z(β)`,

with the left side positive and the coupling negative on `β < 2`: the sign of `Z` on the
strip is carried entirely by the coupling, not by either trace.  The coupling vanishes
exactly at `β = 2` while its Born reflection vanishes exactly at `β = 0`, so the two boundary
poles of `Z` have distinct mechanisms — a grading resonance at one end, the archimedean wall
at the other — and the Born reflection `β ↦ 2 - β` exchanges them.
-/

noncomputable section

namespace RHTower

open Complex

/-! ## The graded supertrace and the eta coupling -/

/-- The graded doublet summand of the half-dilated prime system at inverse temperature `β`:
the parity supertrace of the two levels `{2n+1, 2n+2}` of the Hamiltonian `log √n`. -/
def bornSupertraceTerm (β : ℝ) (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) ^ (-(β / 2)) - (2 * n + 2 : ℝ) ^ (-(β / 2))

/-- The parity-graded supertrace of the half-dilated prime system. -/
def bornSupertrace (β : ℝ) : ℝ := ∑' n : ℕ, bornSupertraceTerm β n

/-- The eta coupling scalar mediating between the graded supertrace and the completed
partition function: the deleted Euler factor at the grading prime `2`. -/
def etaCoupling (β : ℝ) : ℝ := 1 - (2 : ℝ) ^ (1 - β / 2)

theorem bornSupertraceTerm_pos {β : ℝ} (h0 : 0 < β) (n : ℕ) :
    0 < bornSupertraceTerm β n := by
  rw [bornSupertraceTerm]
  exact etaRealTerm_pos (β / 2) (by linarith) n

theorem summable_bornSupertraceTerm {β : ℝ} (h0 : 0 < β) :
    Summable (bornSupertraceTerm β) := by
  rw [← Complex.summable_ofReal]
  apply (summable_etaTerm ((β / 2 : ℝ) : ℂ)
    (by simpa using (by linarith : (0 : ℝ) < β / 2))).congr
  intro n
  rw [etaTerm_ofReal, bornSupertraceTerm]

/-- The graded supertrace converges to a strictly positive value at every inverse
temperature `β > 0` — in particular throughout the strip, where the ungraded trace
diverges. -/
theorem bornSupertrace_pos {β : ℝ} (h0 : 0 < β) : 0 < bornSupertrace β :=
  (summable_bornSupertraceTerm h0).tsum_pos
    (fun n => (bornSupertraceTerm_pos h0 n).le) 0 (bornSupertraceTerm_pos h0 0)

/-- The complex paired eta series at the real argument `β/2` is the cast of the real graded
supertrace. -/
theorem etaPair_ofReal_bornSupertrace (β : ℝ) :
    etaPair ((β / 2 : ℝ) : ℂ) = ((bornSupertrace β : ℝ) : ℂ) := by
  rw [etaPair, bornSupertrace, Complex.ofReal_tsum]
  exact tsum_congr fun n => by rw [etaTerm_ofReal, bornSupertraceTerm]

theorem etaCoupling_cast (β : ℝ) :
    1 - (2 : ℂ) ^ (1 - ((β / 2 : ℝ) : ℂ)) = ((etaCoupling β : ℝ) : ℂ) := by
  have h2 : (2 : ℂ) ^ (1 - ((β / 2 : ℝ) : ℂ)) = (((2 : ℝ) ^ (1 - β / 2) : ℝ) : ℂ) := by
    rw [show (1 - ((β / 2 : ℝ) : ℂ)) = (((1 - β / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h2, etaCoupling]
  push_cast
  ring

theorem etaCoupling_neg {β : ℝ} (h2 : β < 2) : etaCoupling β < 0 := by
  have h : (1 : ℝ) < (2 : ℝ) ^ (1 - β / 2) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  rw [etaCoupling]
  linarith

/-- The eta coupling vanishes exactly at the right end of the temperature strip: the
grading resonance `2^{1-β/2} = 1`. -/
theorem etaCoupling_eq_zero_iff (β : ℝ) : etaCoupling β = 0 ↔ β = 2 := by
  rw [etaCoupling, sub_eq_zero]
  constructor
  · intro h
    have hlog := congrArg Real.log h
    rw [Real.log_one, Real.log_rpow (by norm_num)] at hlog
    have hln2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hz : 1 - β / 2 = 0 := by
      rcases mul_eq_zero.mp hlog.symm with h' | h'
      · exact h'
      · exact absurd h' hln2
    linarith
  · rintro rfl
    rw [show (1 : ℝ) - 2 / 2 = 0 by norm_num, Real.rpow_zero]

/-- The Born reflection of the eta coupling is the deleted factor `1 - 2^{β/2}`. -/
theorem etaCoupling_reflect (β : ℝ) : etaCoupling (2 - β) = 1 - (2 : ℝ) ^ (β / 2) := by
  rw [etaCoupling, show (1 : ℝ) - (2 - β) / 2 = β / 2 by ring]

/-- The reflected coupling vanishes exactly at the left end of the strip: the Born
reflection exchanges the grading resonance at `β = 2` with the archimedean wall at
`β = 0`. -/
theorem etaCoupling_reflect_eq_zero_iff (β : ℝ) : etaCoupling (2 - β) = 0 ↔ β = 0 := by
  rw [etaCoupling_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-! ## The sign of the completed partition function on the strip -/

/-- The completed zeta is a strictly negative real on the real segment of the critical
strip: the polynomial factor of the real-positive `ξ` anchor is negative there. -/
theorem completedRiemannZeta_real_strip_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, x < 0 ∧ completedRiemannZeta (σ : ℂ) = (x : ℂ) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt h0
  have hσ1 : (σ : ℂ) ≠ 1 := by
    rw [Ne, Complex.ofReal_eq_one]
    exact ne_of_lt h1
  have him := xi_real_on_real_anchor h0 h1
  have hxiReal : xi (σ : ℂ) = (((xi (σ : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hwpos : 0 < (xi (σ : ℂ)).re := xi_pos_on_real_anchor h0 h1
  set w : ℝ := (xi (σ : ℂ)).re with hw
  set c : ℝ := σ * (σ - 1) / 2 with hc
  have hcneg : c < 0 := by
    rw [hc]
    apply div_neg_of_neg_of_pos _ two_pos
    exact mul_neg_of_pos_of_neg h0 (by linarith)
  have hcC : (σ : ℂ) * ((σ : ℂ) - 1) / 2 = ((c : ℝ) : ℂ) := by
    rw [hc]
    push_cast
    ring
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_lt hcneg
  have hxi := xi_eq_half_mul hσ0 hσ1
  rw [hxiReal, hcC] at hxi
  refine ⟨w / c, div_neg_of_pos_of_neg hwpos hcneg, ?_⟩
  rw [Complex.ofReal_div, eq_div_iff hcne]
  linear_combination -hxi

/-- The archimedean factor is a strictly positive real on the real segment of the strip:
the ungraded archimedean trace carries no sign. -/
theorem Gammaℝ_real_strip_pos {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ g : ℝ, 0 < g ∧ Complex.Gammaℝ (σ : ℂ) = (g : ℂ) := by
  obtain ⟨Z, hZ, hZeq⟩ := completedRiemannZeta_real_strip_neg h0 h1
  obtain ⟨x, hx, hxeq⟩ := riemannZeta_real_strip_neg h0 h1
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt h0
  have hG : Complex.Gammaℝ (σ : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using h0)
  have hζ := riemannZeta_def_of_ne_zero hσ0
  rw [hxeq, hZeq] at hζ
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_lt hx
  refine ⟨Z / x, div_pos_of_neg_of_neg hZ hx, ?_⟩
  field_simp [hG] at hζ
  rw [Complex.ofReal_div, eq_div_iff hxne]
  linear_combination hζ

/-! ## The eta factorization -/

/-- **The eta factorization of the completed zeta.**  The archimedean factor times the
graded paired eta series equals the eta coupling times the completed partition function. -/
theorem Gammaℝ_mul_etaPair {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    Complex.Gammaℝ s * etaPair s = (1 - (2 : ℂ) ^ (1 - s)) * completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  rw [etaPair_eq s h0 h1, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- **Positive factorization of the Born partition sign on the whole strip.**  For
`0 < β < 2` the half-dilated completed partition function `Z(β) = Λ(β/2)` is a strictly
negative real, and its sign is carried entirely by the eta coupling:
`Z · (coupling) = (archimedean trace) · (graded supertrace)` with both right-hand factors
strictly positive and the coupling strictly negative. -/
theorem bornPartition_positive_factorization {β : ℝ} (h0 : 0 < β) (h2 : β < 2) :
    ∃ Z g : ℝ,
      completedRiemannZeta ((β / 2 : ℝ) : ℂ) = (Z : ℂ)
      ∧ Complex.Gammaℝ ((β / 2 : ℝ) : ℂ) = (g : ℂ)
      ∧ Z < 0 ∧ 0 < g ∧ 0 < bornSupertrace β ∧ etaCoupling β < 0
      ∧ Z * etaCoupling β = g * bornSupertrace β := by
  have hσ0 : 0 < β / 2 := by linarith
  have hσ1 : β / 2 < 1 := by linarith
  obtain ⟨Z, hZ, hZeq⟩ := completedRiemannZeta_real_strip_neg hσ0 hσ1
  obtain ⟨g, hg, hgeq⟩ := Gammaℝ_real_strip_pos hσ0 hσ1
  refine ⟨Z, g, hZeq, hgeq, hZ, hg, bornSupertrace_pos h0, etaCoupling_neg h2, ?_⟩
  have hfact := Gammaℝ_mul_etaPair (s := ((β / 2 : ℝ) : ℂ))
    (by simpa using hσ0) (by rw [Ne, Complex.ofReal_eq_one]; exact ne_of_lt hσ1)
  rw [hgeq, hZeq, etaPair_ofReal_bornSupertrace β, etaCoupling_cast β] at hfact
  have hreal : g * bornSupertrace β = etaCoupling β * Z := by
    exact_mod_cast hfact
  linear_combination -hreal

/-- **The twisted functional equation of the graded object.**  The parity grading pays for
its strip convergence with a broken self-duality: the graded completed object
`Γℝ · etaPair` satisfies the reflection identity only up to the two-adic cocycle
`(1 - 2^s)/(1 - 2^{1-s})`, never the plain functional equation. -/
theorem graded_reflection_cocycle {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (1 - (2 : ℂ) ^ s) * (Complex.Gammaℝ s * etaPair s)
      = (1 - (2 : ℂ) ^ (1 - s)) * (Complex.Gammaℝ (1 - s) * etaPair (1 - s)) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hs1' : (1 : ℂ) - s ≠ 1 := by
    intro h
    have : s = 0 := by linear_combination -h
    rw [this] at h0
    simp at h0
  have hre : 0 < ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [Gammaℝ_mul_etaPair h0 hs1, Gammaℝ_mul_etaPair hre hs1',
    completedRiemannZeta_one_sub, show (1 : ℂ) - (1 - s) = s by ring]
  ring

/-! ## The grading is the parity grading, uniquely -/

/-- The Euler-deletion coefficient at `q`: the `n`-th Dirichlet coefficient of
`(1 - q^{1-s}) · ζ(s)` is `1 - q·[q ∣ n]`. -/
def eulerDeletionCoefficient (q n : ℕ) : ℤ :=
  1 - (q : ℤ) * (if q ∣ n then 1 else 0)

/-- **The parity grading is the unique unimodular Euler deletion.**  The deleted-factor
coefficients take only the values `±1` — i.e. define a `ℤ/2` grading of the integer levels —
exactly for `q = 2`, where the coefficient is `(-1)^{n-1}`. -/
theorem eulerDeletionCoefficient_unimodular_iff {q : ℕ} (hq : 2 ≤ q) :
    (∀ n : ℕ, eulerDeletionCoefficient q n = 1 ∨ eulerDeletionCoefficient q n = -1)
      ↔ q = 2 := by
  constructor
  · intro h
    have hd := h q
    rw [eulerDeletionCoefficient, if_pos dvd_rfl] at hd
    omega
  · rintro rfl n
    rw [eulerDeletionCoefficient]
    split <;> omega

end RHTower
