import GaloisForLFunctions.ArithmeticOrientationTheory.WienersLemmaOnTheBohrPolydisk
import GaloisForLFunctions.ArithmeticOrientationTheory.LocalFactorsAreTheUnitsOfTheWienerMonoid
import GaloisForLFunctions.TransHorizonIncidenceMechanics.LogarithmicMomentHierarchySeparatesEveryPositivePair

/-!
# Units of the Wiener monoid preserve payment

The critical Wiener monoid of real kernels (`CriticalWiener`, `IsWienerUnit`) sits inside the
Banach algebra `𝒲_{1/2}` (`toWiener`), and its units are exactly the units of the Banach algebra
(`isWienerUnit_iff_isUnit`): a real kernel with a complex critical Wiener inverse has a real one,
the real part.  Hence:

* **Wiener's lemma for the critical Wiener monoid** (`isWienerUnit_iff_forall_bohrEval_ne_zero`):
  a real critical Wiener kernel `k` has a critical Wiener inverse iff
  `Σ_n k(n) ω(n) n^{−1/2} ≠ 0` at every point `ω` of the Bohr polydisk.
* **Payment is a unit invariant** (`receiverBounded_dirichletConv_iff_of_isWienerUnit`): for a
  unit `k` and a weight with summable mean, `k ⋆ c` is paid iff `c` is paid.  The units preserve
  the unpaid class as well as the paid class, so the paid/unpaid dichotomy is a union of orbits
  of the unit group, and every finite Euler product `Π (δ₁ − a_p δ_p)` with `|a_p| < √p` and its
  inverse leave the payment status of every weight unchanged.
-/

open Finset ArithmeticFunction LSeries

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Real kernels in `𝒲_{1/2}` -/

/-- A real kernel as a complex arithmetic function (its value at `0` is discarded). -/
def realFn (g : ℕ → ℝ) : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else (g n : ℂ), by simp⟩

theorem realFn_apply {g : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) : realFn g n = (g n : ℂ) := if_neg hn

theorem norm_term_realFn (g : ℕ → ℝ) (n : ℕ) :
    ‖term (⇑(realFn g)) ((1 / 2 : ℝ) : ℂ) n‖ = |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [norm_term_eq, if_neg hn, realFn_apply hn, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem lSeriesSummable_realFn_iff (g : ℕ → ℝ) :
    LSeriesSummable (⇑(realFn g)) ((1 / 2 : ℝ) : ℂ) ↔ CriticalWiener g := by
  rw [← summable_norm_term_iff]
  simp_rw [norm_term_realFn]
  rfl

/-- A critical Wiener kernel as an element of `𝒲_{1/2}`. -/
def toWiener (g : ℕ → ℝ) (hg : CriticalWiener g) : WienerAlgebraAt (1 / 2) :=
  mk (realFn g) ((lSeriesSummable_realFn_iff g).2 hg)

/-- Real Dirichlet convolution is the product of arithmetic functions. -/
theorem realFn_dirichletConv (a b : ℕ → ℝ) :
    realFn (RHTower.dirichletConv a b) = realFn a * realFn b := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [realFn_apply hn, mul_apply, Nat.sum_divisorsAntidiagonal
    (fun i j => realFn a i * realFn b j), RHTower.dirichletConv, Complex.ofReal_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hnd : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  rw [realFn_apply hd0, realFn_apply hnd, Complex.ofReal_mul]

theorem realFn_unitKernel : realFn unitKernel = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [realFn_apply hn, one_apply, unitKernel]
  split_ifs <;> simp

/-- **The units of the critical Wiener monoid are the units of `𝒲_{1/2}`.** -/
theorem isWienerUnit_iff_isUnit (g : ℕ → ℝ) (hg : CriticalWiener g) :
    IsWienerUnit g ↔ IsUnit (toWiener g hg) := by
  constructor
  · rintro ⟨-, h, hh, hinv⟩
    refine isUnit_iff_exists_inv.2 ⟨toWiener h hh, toFn_injective ?_⟩
    rw [toFn_mul, toFn_one]
    show realFn g * realFn h = 1
    rw [← realFn_dirichletConv, ← realFn_unitKernel]
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [realFn_apply hn, realFn_apply hn, hinv n hn]
  · intro hu
    obtain ⟨H, hH⟩ := hu.exists_right_inv
    set h : ℕ → ℝ := fun n => (H.toFn n).re with hh
    have hWh : CriticalWiener h := by
      refine (summable_norm H).of_nonneg_of_le (fun n => by positivity) fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [norm_term_eq, if_neg hn, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
          ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)
    refine ⟨hg, h, hWh, fun n hn => ?_⟩
    have h1 := congrArg (fun f : WienerAlgebraAt (1 / 2) => (f.toFn n).re) hH
    simp only [toFn_mul, toFn_one] at h1
    change ((realFn g * H.toFn) n).re = ((1 : ArithmeticFunction ℂ) n).re at h1
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => realFn g i * H.toFn j),
      Complex.re_sum] at h1
    rw [RHTower.dirichletConv, unitKernel]
    rw [one_apply] at h1
    convert h1 using 1
    · refine sum_congr rfl fun d hd => ?_
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      rw [realFn_apply hd0, Complex.re_ofReal_mul]
    · split_ifs <;> simp

/-- **Wiener's lemma for the critical Wiener monoid.**  A real critical Wiener kernel has a
critical Wiener inverse iff its Bohr evaluation `Σ_n k(n) ω(n) n^{−1/2}` vanishes at no point of
the Bohr polydisk. -/
theorem isWienerUnit_iff_forall_bohrEval_ne_zero (g : ℕ → ℝ) (hg : CriticalWiener g) :
    IsWienerUnit g ↔ ∀ ω : BohrPoint, bohrEval (1 / 2) (realFn g) ω ≠ 0 := by
  rw [isWienerUnit_iff_isUnit g hg, isUnit_iff_forall_bohrEval_ne_zero]
  rfl

/-- **A unit of the critical Wiener monoid has no zero on `Re s ≥ ½`.** -/
theorem lSeries_ne_zero_of_isWienerUnit {g : ℕ → ℝ} (hu : IsWienerUnit g) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : LSeries (fun n => (g n : ℂ)) s ≠ 0 := by
  have h := lSeries_ne_zero_of_isUnit ((isWienerUnit_iff_isUnit g hu.1).1 hu) hs
  rwa [show (⇑(toWiener g hu.1).toFn : ℕ → ℂ) = ⇑(realFn g) from rfl,
    show LSeries (⇑(realFn g)) s = LSeries (fun n => (g n : ℂ)) s from
      LSeries_congr (fun {n} hn => realFn_apply hn) s] at h

/-! ### Payment is a unit invariant -/

/-- Convolution with a critical Wiener kernel keeps the mean summable. -/
theorem summable_abs_dirichletConv_div {g c : ℕ → ℝ} (hg : CriticalWiener g)
    (hc : Summable fun d : ℕ => |c d / d|) :
    Summable fun n : ℕ => |RHTower.dirichletConv g c n / n| := by
  have hg' : Summable fun q : ℕ => |(fun q => |g q|) q / q| := by
    simpa [abs_div] using hg.summable_abs_div
  have hc' : Summable fun d : ℕ => |(fun d => |c d|) d / d| := by
    simpa [abs_div] using hc
  have hs := (hasSum_dirichletConv_div hg'.of_abs.hasSum hc'.of_abs.hasSum hg' hc').summable
  refine hs.of_nonneg_of_le (fun _ => abs_nonneg _) fun n => ?_
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right ((abs_dirichletConv_le g c n).trans (le_of_eq (by
    unfold absConv RHTower.dirichletConv; rfl))) (Nat.cast_nonneg n)

/-- **Units of the critical Wiener monoid preserve payment in both directions**: for a unit `k`
and a weight `c` with summable mean, `k ⋆ c` is paid iff `c` is paid. -/
theorem receiverBounded_dirichletConv_iff_of_isWienerUnit {k c : ℕ → ℝ} (hk : IsWienerUnit k)
    (hc : Summable fun d : ℕ => |c d / d|) :
    ReceiverBounded (RHTower.dirichletConv k c) ↔ ReceiverBounded c := by
  refine ⟨fun h => ?_, fun h => receiverBounded_dirichletConv hk.1 hc h⟩
  obtain ⟨hk1, g, hg, hinv⟩ := hk
  have h2 := receiverBounded_dirichletConv hg (summable_abs_dirichletConv_div hk1 hc) h
  refine (receiverBounded_congr fun n hn => ?_).1 h2
  rw [← dirichletConv_assoc, dirichletConv_comm g k,
    dirichletConv_congr (fun m hm => hinv m hm) (fun _ _ => rfl) n,
    dirichletConv_unitKernel c hn.ne']

/-- **The unpaid class is a union of unit orbits.** -/
theorem not_receiverBounded_dirichletConv_iff_of_isWienerUnit {k c : ℕ → ℝ}
    (hk : IsWienerUnit k) (hc : Summable fun d : ℕ => |c d / d|) :
    ¬ ReceiverBounded (RHTower.dirichletConv k c) ↔ ¬ ReceiverBounded c :=
  not_congr (receiverBounded_dirichletConv_iff_of_isWienerUnit hk hc)

end

end GaloisForLFunctions.ArithmeticOrientationTheory
