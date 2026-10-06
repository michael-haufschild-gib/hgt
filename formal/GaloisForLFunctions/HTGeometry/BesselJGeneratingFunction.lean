import GaloisForLFunctions.HTGeometry.PoincareSeriesBesselCoefficient

/-!
# The generating function of the integer-order Bessel functions

For `J_l(x) = Σ_j (−1)^j (x/2)^{2j+l}/(j!(j+l)!)` (`besselJ`, `l ∈ ℕ`), extended by `J_{−l} = (−1)^l J_l`
(`besselJInt`):

* `|J_l(x)| ≤ |x/2|^l/l! · e^{(x/2)²}` (`abs_besselJ_le`);
* **the generating function**: for `t ≠ 0`, `Σ_{l∈ℤ} J_l(x) t^l = exp((x/2)(t − t⁻¹))`
  (`hasSum_besselJInt_generating`), from the Cauchy product of `exp(xt/2)` and `exp(−x/(2t))` reindexed by
  `(a, b) ↦ (a − b, min(a, b))`;
* **Jacobi–Anger** for complex `θ`: `sin(x sin θ) = 2 Σ_{k} J_{2k+1}(x) sin((2k+1)θ)`
  (`hasSum_sin_mul_sin`).
-/

open Complex
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## A bound for `J_l` -/

theorem abs_besselJ_term_le (l : ℕ) (x : ℝ) (j : ℕ) :
    |(-1 : ℝ) ^ j * (x / 2) ^ (2 * j + l) / ((j.factorial : ℝ) * ((j + l).factorial : ℝ))| ≤
      |x / 2| ^ l / l.factorial * (((x / 2) ^ 2) ^ j / j.factorial) := by
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hl : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  have hjl : (l.factorial : ℝ) ≤ (j + l).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_left l j)
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (j.factorial : ℝ) * ((j + l).factorial : ℝ))]
  have hsq : |x / 2| ^ (2 * j + l) = |x / 2| ^ l * ((x / 2) ^ 2) ^ j := by
    rw [pow_add, pow_mul, sq_abs, mul_comm]
  rw [hsq, div_le_iff₀ (by positivity)]
  have hA : 0 ≤ |x / 2| ^ l * ((x / 2) ^ 2) ^ j := by positivity
  calc |x / 2| ^ l * ((x / 2) ^ 2) ^ j
      = |x / 2| ^ l / l.factorial * (((x / 2) ^ 2) ^ j / j.factorial) *
          ((j.factorial : ℝ) * l.factorial) := by field_simp
    _ ≤ _ := by gcongr

theorem hasSum_real_exp_series (y : ℝ) : HasSum (fun n : ℕ => y ^ n / n.factorial) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

/-- **`|J_l(x)| ≤ |x/2|^l/l! · e^{(x/2)²}`.** -/
theorem abs_besselJ_le (l : ℕ) (x : ℝ) :
    |besselJ l x| ≤ |x / 2| ^ l / l.factorial * Real.exp ((x / 2) ^ 2) := by
  have hs := (hasSum_real_exp_series ((x / 2) ^ 2)).mul_left (|x / 2| ^ l / l.factorial)
  rw [besselJ, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hs fun j => abs_besselJ_term_le l x j

theorem besselJ_neg (l : ℕ) (x : ℝ) : besselJ l (-x) = (-1) ^ l * besselJ l x := by
  rw [besselJ, besselJ, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [neg_div, neg_pow (x / 2), pow_add (-1 : ℝ) (2 * j) l, pow_mul, neg_one_sq, one_pow, one_mul]
  ring

/-! ## The generating function -/

/-- `J_l` for `l ∈ ℤ`: `J_{−l} = (−1)^l J_l`. -/
def besselJInt (l : ℤ) (x : ℝ) : ℝ :=
  Int.rec (fun n => besselJ n x) (fun n => (-1) ^ (n + 1) * besselJ (n + 1) x) l

theorem hasSum_cexp_series (z : ℂ) : HasSum (fun n : ℕ => z ^ n / n.factorial) (cexp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- The reindexing `ℕ × ℕ ≃ ℤ × ℕ`, `(a, b) ↦ (a − b, min(a, b))`. -/
def diffMinEquiv : ℕ × ℕ ≃ ℤ × ℕ where
  toFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  invFun q := (q.2 + q.1.toNat, q.2 + (-q.1).toNat)
  left_inv p := by
    rcases p with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    constructor <;> omega
  right_inv q := by
    rcases q with ⟨l, m⟩
    simp only [Prod.mk.injEq]
    constructor <;> omega

theorem fibre_nonneg (x : ℝ) {t : ℂ} (ht : t ≠ 0) (n m : ℕ) :
    ((x / 2 : ℂ) * t) ^ (m + n) / ((m + n).factorial : ℂ) *
        ((-((x / 2 : ℂ) * t⁻¹)) ^ m / (m.factorial : ℂ)) =
      ((((-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) /
        ((m.factorial : ℝ) * ((m + n).factorial : ℝ))) : ℝ) : ℂ) * t ^ (Int.ofNat n : ℤ) := by
  rw [Int.ofNat_eq_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, neg_pow, mul_pow, inv_pow, show 2 * m + n = (m + n) + m by ring, pow_add (x / 2 : ℂ),
    pow_add t m n]
  have htm : t ^ m ≠ 0 := pow_ne_zero m ht
  field_simp
  ring

theorem fibre_neg (x : ℝ) {t : ℂ} (ht : t ≠ 0) (n m : ℕ) :
    ((x / 2 : ℂ) * t) ^ m / (m.factorial : ℂ) *
        ((-((x / 2 : ℂ) * t⁻¹)) ^ (m + (n + 1)) / ((m + (n + 1)).factorial : ℂ)) =
      ((((-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ m * (x / 2) ^ (2 * m + (n + 1)) /
        ((m.factorial : ℝ) * ((m + (n + 1)).factorial : ℝ)))) : ℝ) : ℂ) * t ^ (Int.negSucc n) := by
  rw [zpow_negSucc]
  push_cast
  rw [mul_pow, neg_pow, mul_pow, inv_pow, show 2 * m + (n + 1) = m + (m + (n + 1)) by ring,
    pow_add (x / 2 : ℂ), pow_add t m (n + 1), pow_add (-1 : ℂ) m (n + 1)]
  have htm : t ^ m ≠ 0 := pow_ne_zero m ht
  have htn : t ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) ht
  field_simp
  ring

/-- **The Bessel generating function**: `Σ_{l∈ℤ} J_l(x) t^l = exp((x/2)(t − t⁻¹))`, `t ≠ 0`. -/
theorem hasSum_besselJInt_generating (x : ℝ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun l : ℤ => (besselJInt l x : ℂ) * t ^ l) (cexp ((x / 2 : ℂ) * (t - t⁻¹))) := by
  set u : ℂ := (x / 2 : ℂ) * t
  set w : ℂ := -((x / 2 : ℂ) * t⁻¹)
  have hexp : cexp ((x / 2 : ℂ) * (t - t⁻¹)) = cexp u * cexp w := by
    rw [← Complex.exp_add]; congr 1; simp only [u, w]; ring
  set f : ℕ → ℂ := fun n => u ^ n / n.factorial with hf
  set g : ℕ → ℂ := fun n => w ^ n / n.factorial with hg
  have hu : HasSum f (cexp u) := hasSum_cexp_series u
  have hw : HasSum g (cexp w) := hasSum_cexp_series w
  have hnu : Summable fun n : ℕ => ‖f n‖ := by
    simpa [f, norm_div, norm_pow] using Real.summable_pow_div_factorial ‖u‖
  have hnw : Summable fun n : ℕ => ‖g n‖ := by
    simpa [g, norm_div, norm_pow] using Real.summable_pow_div_factorial ‖w‖
  have hprod0 : HasSum (fun p : ℕ × ℕ => f p.1 * g p.2) (cexp u * cexp w) :=
    hu.mul hw (summable_mul_of_summable_norm (f := f) (g := g) hnu hnw)
  rw [← hexp] at hprod0
  have hprod := (Equiv.hasSum_iff diffMinEquiv.symm).2 hprod0
  refine hprod.prod_fiberwise fun l => ?_
  -- the fibre over `l`
  rcases l with n | n
  · -- `l = n ≥ 0`
    have hsymm : ∀ m : ℕ, diffMinEquiv.symm ((Int.ofNat n : ℤ), m) = (m + n, m) := fun m => by
      simp only [diffMinEquiv, Equiv.coe_fn_symm_mk, Int.ofNat_eq_natCast, Int.toNat_natCast, Prod.mk.injEq,
        true_and]
      omega
    have hfib : ∀ m : ℕ, ((fun p : ℕ × ℕ => f p.1 * g p.2) ∘ diffMinEquiv.symm)
        ((Int.ofNat n : ℤ), m) =
        ((((-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) /
          ((m.factorial : ℝ) * ((m + n).factorial : ℝ))) : ℝ) : ℂ) * t ^ (Int.ofNat n : ℤ) := fun m => by
      simp only [Function.comp_apply, hsymm m, f, g]
      exact fibre_nonneg x ht n m
    simp_rw [hfib]
    have hJ := (summable_besselJ_term n x).hasSum
    have h2 := (hJ.mapL Complex.ofRealCLM).mul_right (t ^ (Int.ofNat n : ℤ))
    have e : besselJInt (Int.ofNat n) x = besselJ n x := rfl
    rw [e, besselJ]
    exact h2
  · -- `l = −(n+1) < 0`
    have hsymm : ∀ m : ℕ, diffMinEquiv.symm (Int.negSucc n, m) = (m, m + (n + 1)) := fun m => by
      simp only [diffMinEquiv, Equiv.coe_fn_symm_mk, Prod.mk.injEq]
      constructor <;> omega
    have hfib : ∀ m : ℕ, ((fun p : ℕ × ℕ => f p.1 * g p.2) ∘ diffMinEquiv.symm)
        (Int.negSucc n, m) =
        ((((-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ m * (x / 2) ^ (2 * m + (n + 1)) /
          ((m.factorial : ℝ) * ((m + (n + 1)).factorial : ℝ)))) : ℝ) : ℂ) *
            t ^ (Int.negSucc n) := fun m => by
      simp only [Function.comp_apply, hsymm m, f, g]
      exact fibre_neg x ht n m
    simp_rw [hfib]
    have hJ := (summable_besselJ_term (n + 1) x).hasSum.mul_left ((-1 : ℝ) ^ (n + 1))
    have h2 := (hJ.mapL Complex.ofRealCLM).mul_right (t ^ (Int.negSucc n))
    have e : besselJInt (Int.negSucc n) x = (-1) ^ (n + 1) * besselJ (n + 1) x := rfl
    rw [e, besselJ]
    exact h2


/-! ## Jacobi–Anger -/

theorem besselJInt_negSucc (n : ℕ) (x : ℝ) :
    besselJInt (Int.negSucc n) x = (-1) ^ (n + 1) * besselJ (n + 1) x := rfl

theorem besselJInt_ofNat (n : ℕ) (x : ℝ) : besselJInt (n : ℤ) x = besselJ n x := rfl

theorem summable_abs_besselJ_mul_pow (x r : ℝ) :
    Summable fun n : ℕ => |besselJ n x| * r ^ n := by
  have hs := (Real.summable_pow_div_factorial (|x / 2| * |r|)).mul_right (Real.exp ((x / 2) ^ 2))
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow]
  calc |besselJ n x| * |r| ^ n ≤ |x / 2| ^ n / n.factorial * Real.exp ((x / 2) ^ 2) * |r| ^ n := by
        gcongr; exact abs_besselJ_le n x
    _ = _ := by rw [mul_pow]; ring

/-- The odd part of the generating series. -/
def jacobiAngerTerm (x : ℝ) (t : ℂ) (l : ℤ) : ℂ :=
  ((besselJInt l x - besselJInt l (-x) : ℝ) : ℂ) * t ^ l / (2 * Complex.I)

theorem summable_jacobiAngerTerm (x : ℝ) {t : ℂ} (ht : t ≠ 0) :
    Summable (jacobiAngerTerm x t) := by
  set ρ := max ‖t‖ ‖t‖⁻¹
  have hρ : 0 < ρ := lt_max_of_lt_left (norm_pos_iff.2 ht)
  have hB : Summable fun n : ℕ => (|besselJ n x| + |besselJ n (-x)|) * ρ ^ n :=
    ((summable_abs_besselJ_mul_pow x ρ).add (summable_abs_besselJ_mul_pow (-x) ρ)).congr
      fun n => by ring
  have h2 : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by simp
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_norm_bounded (hB.mul_left (1 / 2)) fun n => ?_
    rw [jacobiAngerTerm, div_eq_mul_inv, norm_mul, norm_mul, h2, Complex.norm_real, zpow_natCast,
      norm_pow, besselJInt_ofNat, besselJInt_ofNat, Real.norm_eq_abs]
    have : ‖t‖ ^ n ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) n
    have habs := abs_sub (besselJ n x) (besselJ n (-x))
    calc |besselJ n x - besselJ n (-x)| * ‖t‖ ^ n * (1 / 2) ≤
          (|besselJ n x| + |besselJ n (-x)|) * ρ ^ n * (1 / 2) := by gcongr
      _ = _ := by ring
  · refine Summable.of_norm_bounded ((hB.comp_injective (add_left_injective 1)).mul_left (1 / 2))
      fun n => ?_
    rw [show -((n : ℤ) + 1) = Int.negSucc n from rfl, jacobiAngerTerm, div_eq_mul_inv, norm_mul,
      norm_mul, h2, Complex.norm_real, zpow_negSucc, norm_inv, norm_pow, besselJInt_negSucc,
      besselJInt_negSucc, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
    have : (‖t‖ ^ (n + 1))⁻¹ ≤ ρ ^ (n + 1) := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    have habs := abs_sub (besselJ (n + 1) x) (besselJ (n + 1) (-x))
    simp only [Function.comp_apply]
    calc |besselJ (n + 1) x - besselJ (n + 1) (-x)| * (‖t‖ ^ (n + 1))⁻¹ * (1 / 2) ≤
          (|besselJ (n + 1) x| + |besselJ (n + 1) (-x)|) * ρ ^ (n + 1) * (1 / 2) := by gcongr
      _ = _ := by ring

theorem hasSum_jacobiAngerTerm (x : ℝ) (θ : ℂ) :
    HasSum (jacobiAngerTerm x (cexp (θ * Complex.I))) (Complex.sin (x * Complex.sin θ)) := by
  have ht : cexp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have htt : cexp (θ * Complex.I) - (cexp (θ * Complex.I))⁻¹ = 2 * Complex.I * Complex.sin θ := by
    rw [Complex.sin, ← Complex.exp_neg]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hS := ((hasSum_besselJInt_generating x ht).sub
    (hasSum_besselJInt_generating (-x) ht)).div_const (2 * Complex.I)
  have hfun : (fun l : ℤ => ((besselJInt l x : ℂ) * cexp (θ * Complex.I) ^ l -
      (besselJInt l (-x) : ℂ) * cexp (θ * Complex.I) ^ l) / (2 * Complex.I)) =
      jacobiAngerTerm x (cexp (θ * Complex.I)) := funext fun l => by
    simp only [jacobiAngerTerm]; push_cast; ring
  have e1 : (x : ℂ) / 2 * (2 * Complex.I * Complex.sin θ) = (x * Complex.sin θ) * Complex.I := by ring
  have e2 : ((-x : ℝ) : ℂ) / 2 * (2 * Complex.I * Complex.sin θ) =
      -((x * Complex.sin θ) * Complex.I) := by push_cast; ring
  have hval : (cexp ((x : ℂ) / 2 * (cexp (θ * Complex.I) - (cexp (θ * Complex.I))⁻¹)) -
      cexp (((-x : ℝ) : ℂ) / 2 * (cexp (θ * Complex.I) - (cexp (θ * Complex.I))⁻¹))) / (2 * Complex.I) =
      Complex.sin (x * Complex.sin θ) := by
    rw [htt, e1, e2]
    generalize (x : ℂ) * Complex.sin θ = z
    rw [Complex.sin, show -z * Complex.I = -(z * Complex.I) by ring]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  rw [hfun, hval] at hS
  exact hS

theorem besselJ_neg_odd (k : ℕ) (x : ℝ) : besselJ (2 * k + 1) (-x) = -besselJ (2 * k + 1) x := by
  rw [besselJ_neg, pow_succ, pow_mul]; norm_num

theorem jacobiAngerTerm_even (x : ℝ) (t : ℂ) (k : ℕ) :
    jacobiAngerTerm x t ((2 * k : ℕ) : ℤ) = 0 := by
  rw [jacobiAngerTerm, besselJInt_ofNat, besselJInt_ofNat, besselJ_neg, pow_mul]
  norm_num

theorem jacobiAngerTerm_negSucc_odd (x : ℝ) (t : ℂ) (k : ℕ) :
    jacobiAngerTerm x t (Int.negSucc (2 * k + 1)) = 0 := by
  rw [jacobiAngerTerm, besselJInt_negSucc, besselJInt_negSucc, besselJ_neg,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
  norm_num

theorem jacobiAngerTerm_pair (x : ℝ) (θ : ℂ) (k : ℕ) :
    jacobiAngerTerm x (cexp (θ * Complex.I)) ((2 * k + 1 : ℕ) : ℤ) +
      jacobiAngerTerm x (cexp (θ * Complex.I)) (Int.negSucc (2 * k)) =
        2 * (besselJ (2 * k + 1) x : ℂ) * Complex.sin ((2 * k + 1 : ℕ) * θ) := by
  have h1 : besselJInt ((2 * k + 1 : ℕ) : ℤ) x - besselJInt ((2 * k + 1 : ℕ) : ℤ) (-x) =
      2 * besselJ (2 * k + 1) x := by
    rw [besselJInt_ofNat, besselJInt_ofNat, besselJ_neg_odd]; ring
  have h2 : besselJInt (Int.negSucc (2 * k)) x - besselJInt (Int.negSucc (2 * k)) (-x) =
      -(2 * besselJ (2 * k + 1) x) := by
    rw [besselJInt_negSucc, besselJInt_negSucc, besselJ_neg_odd, pow_succ, pow_mul]; norm_num; ring
  have hp : cexp (θ * Complex.I) ^ ((2 * k + 1 : ℕ) : ℤ) = cexp (((2 * k + 1 : ℕ) : ℂ) * θ * Complex.I) := by
    rw [zpow_natCast, ← Complex.exp_nat_mul]; congr 1; ring
  have hm : cexp (θ * Complex.I) ^ (Int.negSucc (2 * k)) =
      cexp (-(((2 * k + 1 : ℕ) : ℂ) * θ) * Complex.I) := by
    rw [zpow_negSucc, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  rw [jacobiAngerTerm, jacobiAngerTerm, h1, h2, hp, hm, Complex.sin]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

theorem tsum_jacobiAngerTerm_eq (x : ℝ) {t : ℂ} (ht : t ≠ 0) :
    Summable (fun k : ℕ => jacobiAngerTerm x t ((2 * k + 1 : ℕ) : ℤ) +
        jacobiAngerTerm x t (Int.negSucc (2 * k))) ∧
      ∑' l : ℤ, jacobiAngerTerm x t l = ∑' k : ℕ, (jacobiAngerTerm x t ((2 * k + 1 : ℕ) : ℤ) +
        jacobiAngerTerm x t (Int.negSucc (2 * k))) := by
  have hs := summable_jacobiAngerTerm x ht
  have hnat : Summable fun n : ℕ => jacobiAngerTerm x t n := hs.comp_injective Nat.cast_injective
  have hneg : Summable fun n : ℕ => jacobiAngerTerm x t (Int.negSucc n) :=
    hs.comp_injective (i := Int.negSucc) fun a b h => Int.negSucc.inj h
  have hev : Summable fun k : ℕ => jacobiAngerTerm x t ((2 * k : ℕ) : ℤ) :=
    hnat.comp_injective (i := fun k : ℕ => 2 * k) fun a b h => by simp only at h; omega
  have hod : Summable fun k : ℕ => jacobiAngerTerm x t ((2 * k + 1 : ℕ) : ℤ) :=
    hnat.comp_injective (i := fun k : ℕ => 2 * k + 1) fun a b h => by simp only at h; omega
  have hnev : Summable fun k : ℕ => jacobiAngerTerm x t (Int.negSucc (2 * k)) :=
    hneg.comp_injective (i := fun k : ℕ => 2 * k) fun a b h => by simp only at h; omega
  have hnod : Summable fun k : ℕ => jacobiAngerTerm x t (Int.negSucc (2 * k + 1)) :=
    hneg.comp_injective (i := fun k : ℕ => 2 * k + 1) fun a b h => by simp only at h; omega
  refine ⟨hod.add hnev, ?_⟩
  have hneg' : Summable fun n : ℕ => jacobiAngerTerm x t (-((n : ℤ) + 1)) := hneg
  rw [tsum_of_nat_of_neg_add_one hnat hneg']
  have e1 : ∑' n : ℕ, jacobiAngerTerm x t n =
      ∑' k : ℕ, jacobiAngerTerm x t ((2 * k + 1 : ℕ) : ℤ) := by
    rw [← tsum_even_add_odd (f := fun n : ℕ => jacobiAngerTerm x t n) (by simpa using hev)
      (by simpa using hod)]
    have : ∀ k : ℕ, jacobiAngerTerm x t ((2 * k : ℕ) : ℤ) = 0 := jacobiAngerTerm_even x t
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at this ⊢
    simp only [this, tsum_zero, zero_add]
  have e2 : ∑' n : ℕ, jacobiAngerTerm x t (-((n : ℤ) + 1)) =
      ∑' k : ℕ, jacobiAngerTerm x t (Int.negSucc (2 * k)) := by
    change ∑' n : ℕ, jacobiAngerTerm x t (Int.negSucc n) = _
    rw [← tsum_even_add_odd (f := fun n : ℕ => jacobiAngerTerm x t (Int.negSucc n)) hnev hnod]
    simp only [jacobiAngerTerm_negSucc_odd, tsum_zero, add_zero]
  rw [e1, e2, hod.tsum_add hnev]

/-- **Jacobi–Anger** for complex `θ`: `sin(x sin θ) = 2 Σ_k J_{2k+1}(x) sin((2k+1)θ)`. -/
theorem hasSum_sin_mul_sin (x : ℝ) (θ : ℂ) :
    HasSum (fun k : ℕ => 2 * (besselJ (2 * k + 1) x : ℂ) * Complex.sin ((2 * k + 1 : ℕ) * θ))
      (Complex.sin (x * Complex.sin θ)) := by
  have ht : cexp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨hsum, heq⟩ := tsum_jacobiAngerTerm_eq x ht
  have hval := (hasSum_jacobiAngerTerm x θ).tsum_eq
  rw [heq] at hval
  rw [← hval]
  exact hsum.hasSum.congr_fun fun k => (jacobiAngerTerm_pair x θ k).symm


/-! ## Bessel's integral for odd order -/

/-- Real form of Jacobi–Anger: `sin(x sin θ) = 2 Σ_k J_{2k+1}(x) sin((2k+1)θ)`. -/
theorem hasSum_real_sin_mul_sin (x θ : ℝ) :
    HasSum (fun k : ℕ => 2 * besselJ (2 * k + 1) x * Real.sin ((2 * k + 1 : ℕ) * θ))
      (Real.sin (x * Real.sin θ)) := by
  have h := hasSum_sin_mul_sin x θ
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext k; push_cast; ring
  · push_cast; rfl

theorem integral_cos_nat_mul_pi_div_two (n : ℕ) (hn : n ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos ((2 * n : ℕ) * θ) = 0 := by
  have hc : ((2 * n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * n ≠ 0)
  rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.cos θ) hc, integral_cos, mul_zero,
    Real.sin_zero, sub_zero, show ((2 * n : ℕ) : ℝ) * (Real.pi / 2) = (n : ℝ) * Real.pi by
      push_cast; ring, Real.sin_nat_mul_pi, smul_zero]

/-- `∫_0^{π/2} sin((2k+1)θ) sin((2m+1)θ) dθ = (π/4) δ_{km}`. -/
theorem integral_sin_odd_mul_sin_odd (k m : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin ((2 * m + 1 : ℕ) * θ) =
      if k = m then Real.pi / 4 else 0 := by
  have hprod : ∀ θ : ℝ, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin ((2 * m + 1 : ℕ) * θ) =
      (Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ - ((2 * m + 1 : ℕ) : ℝ) * θ) -
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ + ((2 * m + 1 : ℕ) : ℝ) * θ)) / 2 := fun θ => by
    rw [Real.cos_sub, Real.cos_add]; ring
  simp_rw [hprod]
  have hsum : ∀ θ : ℝ, ((2 * k + 1 : ℕ) : ℝ) * θ + ((2 * m + 1 : ℕ) : ℝ) * θ =
      ((2 * (k + m + 1) : ℕ) : ℝ) * θ := fun θ => by push_cast; ring
  simp_rw [hsum]
  have hI2 : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos (((2 * (k + m + 1) : ℕ) : ℝ) * θ) = 0 :=
    integral_cos_nat_mul_pi_div_two (k + m + 1) (by omega)
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    hI2, sub_zero]
  split_ifs with h
  · subst h; simp; ring
  · rcases lt_or_gt_of_ne h with hlt | hlt
    · have e : ∀ θ : ℝ, ((2 * k + 1 : ℕ) : ℝ) * θ - ((2 * m + 1 : ℕ) : ℝ) * θ =
          -(((2 * (m - k) : ℕ) : ℝ) * θ) := fun θ => by
        rw [Nat.cast_mul, Nat.cast_sub hlt.le]; push_cast; ring
      simp_rw [e, Real.cos_neg]
      rw [integral_cos_nat_mul_pi_div_two (m - k) (by omega), zero_div]
    · have e : ∀ θ : ℝ, ((2 * k + 1 : ℕ) : ℝ) * θ - ((2 * m + 1 : ℕ) : ℝ) * θ =
          ((2 * (k - m) : ℕ) : ℝ) * θ := fun θ => by
        rw [Nat.cast_mul, Nat.cast_sub hlt.le]; push_cast; ring
      simp_rw [e]
      rw [integral_cos_nat_mul_pi_div_two (k - m) (by omega), zero_div]

/-- **Bessel's integral, odd order**: `J_{2k+1}(x) = (2/π) ∫_0^{π/2} sin((2k+1)θ) sin(x sin θ) dθ`. -/
theorem besselJ_odd_eq_integral (k : ℕ) (x : ℝ) :
    besselJ (2 * k + 1) x = 2 / Real.pi *
      ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (x * Real.sin θ) := by
  have hb := (summable_abs_besselJ_mul_pow x 1).comp_injective
    (i := fun m : ℕ => 2 * m + 1) (fun a b h => by simp only at h; omega)
  have hH := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := Real.pi / 2)
    (F := fun m : ℕ => fun θ : ℝ => Real.sin ((2 * k + 1 : ℕ) * θ) *
      (2 * besselJ (2 * m + 1) x * Real.sin ((2 * m + 1 : ℕ) * θ)))
    (f := fun θ : ℝ => Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (x * Real.sin θ))
    (fun m _ => 2 * |besselJ (2 * m + 1) x|)
    (fun m => (by fun_prop : Continuous fun θ : ℝ => Real.sin ((2 * k + 1 : ℕ) * θ) *
      (2 * besselJ (2 * m + 1) x * Real.sin ((2 * m + 1 : ℕ) * θ))).aestronglyMeasurable)
    (fun m => MeasureTheory.ae_of_all _ fun θ _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_two]
      have h1 := Real.abs_sin_le_one (((2 * k + 1 : ℕ) : ℝ) * θ)
      have h2 := Real.abs_sin_le_one (((2 * m + 1 : ℕ) : ℝ) * θ)
      have h3 := abs_nonneg (besselJ (2 * m + 1) x)
      have h4 := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤
        2 * |besselJ (2 * m + 1) x|)) (by positivity) zero_le_one
      linarith)
    (MeasureTheory.ae_of_all _ fun θ _ => by
      simpa using hb.mul_left 2)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ => (hasSum_real_sin_mul_sin x θ).mul_left _)
  have hterm : ∀ m : ℕ, ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) *
      (2 * besselJ (2 * m + 1) x * Real.sin ((2 * m + 1 : ℕ) * θ)) =
      if m = k then 2 * besselJ (2 * k + 1) x * (Real.pi / 4) else 0 := fun m => by
    have : (fun θ : ℝ => Real.sin ((2 * k + 1 : ℕ) * θ) *
        (2 * besselJ (2 * m + 1) x * Real.sin ((2 * m + 1 : ℕ) * θ))) = fun θ =>
        2 * besselJ (2 * m + 1) x * (Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin ((2 * m + 1 : ℕ) * θ)) := by
      funext θ; ring
    rw [this, intervalIntegral.integral_const_mul, integral_sin_odd_mul_sin_odd]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero]
  simp_rw [hterm] at hH
  have := hH.unique (hasSum_ite_eq k (2 * besselJ (2 * k + 1) x * (Real.pi / 4)))
  rw [this]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
