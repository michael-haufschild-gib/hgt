import GaloisForLFunctions.OrderSixMetaplecticTheory.ComplexConjugationActsOnTheCubicSymbols
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CoprimalityMasksAndSexticRows

/-!
# The order-six family is orthogonal to the untwisted theta square

At column `1` the row root number is `Φ(c) = Γ(c) χ₂(c) G̃(c)²` (`rowRootNumber_eq_weil_mul_cubicTwo`): the
squared normalized cubic Gauss sum times a **2-adic phase**, the Weil index `Γ(c)` (a function of `c` modulo
`4`) times the cubic character `χ₂(c) = (c/−2)₃²` of conductor `2`.

The Weil index is invariant under the unit rotation `c ↦ ωc` (`fixedDualAverage_omega_mul`: the three
nontrivial dual phases are permuted), while `χ₂(ω) = ω̄² ≠ 1` (`cubicTwoChar_omega`). Hence `χ₂` is orthogonal to every `ω`-invariant function modulo `4`
(`sum_mul_cubicTwoChar_eq_zero`), and the 2-adic phase has **mean zero** over the residues modulo `4`, at column
`1` (`sum_fixedDualAverage_mul_cubicTwoChar`) and at every column `n`, where the column law multiplies it by the
quadratic bicharacter `\overline{r(n, c)}` (`sum_column_phase_mul_cubicTwoChar`).

Consequence. Expand `Γχ₂` over the characters of `(O/4)^×`: the trivial character has coefficient `0`. So
`Σ Φ(c) N(c)^{−w}` is a combination of the theta-square series `Σ ψ(c) G̃(c)² N(c)^{−w}` twisted by characters
`ψ` **ramified at `2`** only. The untwisted square `S₁` and every twist unramified at `2` (the nine 3-adic
twists) have coefficient zero: the positive main term of `S₁` is not a main term of the order-six family, which
needs the 2-ramified twists of the theta square — at every column.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

/-! ### The cubic character of conductor `2` -/

/-- `χ₂(c) = (c/−2)₃²`, the cubic character of conductor `2` carried by the conductor phase. -/
def cubicTwoChar (c : O) : ℂ := ringComplex (symbol c (-2)) ^ 2

theorem cubicTwoChar_mul (a b : O) : cubicTwoChar (a * b) = cubicTwoChar a * cubicTwoChar b := by
  unfold cubicTwoChar
  rw [symbol_mul_numerator, map_mul, mul_pow]

theorem cubicTwoChar_congr {a b : O} (h : (2 : O) ∣ a - b) : cubicTwoChar a = cubicTwoChar b := by
  unfold cubicTwoChar
  rw [symbol_congr (show (-2 : O) ∣ a - b from (neg_dvd).mpr h)]

theorem absNorm_span_neg_two : Ideal.absNorm (Ideal.span {(-2 : O)}) = 4 := by
  have h := ringComplex_norm_sq_eq_absNorm_span (-2)
  rw [map_neg, map_ofNat, norm_neg, Complex.norm_ofNat] at h
  have h' : ((Ideal.absNorm (Ideal.span {(-2 : O)}) : ℕ) : ℝ) = 4 := by rw [← h]; norm_num
  exact_mod_cast h'

/-- **`(ω/−2)₃ = ω`**: the residue field at `2` has four elements, so Euler's exponent is `1`. -/
theorem symbol_omega_neg_two : symbol omega (-2) = omega := by
  haveI hmax : (Ideal.span {(-2 : O)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible CanonicalRowCompletion.negative_two_prime.irreducible
  have hgood : lambda ∉ Ideal.span {(-2 : O)} :=
    primary_maximal_divisor_good (-2) primary_neg_two _ (Ideal.subset_span rfl)
  rw [symbol_prime (-2) CanonicalRowCompletion.negative_two_prime primary_neg_two, primeValue_eq _ hgood]
  have hcard : Nat.card (O ⧸ Ideal.span {(-2 : O)}) = 4 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_span_neg_two]
  apply reduce_injective_on_roots _ hgood (cubicChar_values _ _ _) (Or.inr ⟨1, by norm_num, (pow_one _).symm⟩)
  rw [cubicChar_reduce, hcard]
  norm_num

theorem cubicTwoChar_omega : cubicTwoChar omega = ringComplex omega ^ 2 := by
  rw [cubicTwoChar, symbol_omega_neg_two]

theorem cubicTwoChar_omega_ne_one : cubicTwoChar omega ≠ 1 := by
  rw [cubicTwoChar_omega]
  intro h
  have h3 : ringComplex omega ^ 3 = 1 := by rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have h1 : ringComplex omega = 1 := by
    calc ringComplex omega = ringComplex omega * ringComplex omega ^ 2 := by rw [h, mul_one]
      _ = ringComplex omega ^ 3 := by ring
      _ = 1 := h3
  exact omega_primitive.ne_one (by norm_num) (ringComplex_injective (h1.trans (map_one _).symm))

/-! ### The Weil index is invariant under the unit rotation -/

theorem omega_mul_eval (a b : ℤ) : omega * Coordinates.eval a b = Coordinates.eval (-b) (a - b) := by
  unfold Coordinates.eval
  push_cast
  linear_combination (b : O) * omega_sq_add

/-- **`Γ(ωc) = Γ(c)`**: the rotation permutes the three nontrivial dual phases. -/
theorem fixedDualAverage_omega_mul (c : O) : fixedDualAverage (omega * c) = fixedDualAverage c := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates c
  change fixedDualAverage (omega * Coordinates.eval a b) = fixedDualAverage (Coordinates.eval a b)
  rw [omega_mul_eval, fixedDualAverage_formula, fixedDualAverage_formula]
  congr 1
  rw [show a - b - -b = a by ring, show -(a - b) = b - a by ring]
  ring

/-! ### Mean zero modulo `4` -/

local instance : Finite (O ⧸ Ideal.span {(4 : O)}) :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))

local instance : Fintype (O ⧸ Ideal.span {(4 : O)}) := Fintype.ofFinite _

/-- A representative of a residue modulo `4`. -/
def rep4 (c : O ⧸ Ideal.span {(4 : O)}) : O := Classical.choose (Ideal.Quotient.mk_surjective c)

theorem mk_rep4 (c : O ⧸ Ideal.span {(4 : O)}) : Ideal.Quotient.mk _ (rep4 c) = c :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective c)

/-- **`χ₂` is orthogonal to every `ω`-invariant function modulo `4`:** if `f` depends on `c` modulo `4` and
`f(ωc) = f(c)`, then `Σ_{c mod 4} f(c) χ₂(c) = 0`. -/
theorem sum_mul_cubicTwoChar_eq_zero (f : O → ℂ)
    (hf4 : ∀ c d : O, Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = Ideal.Quotient.mk _ d → f c = f d)
    (hfω : ∀ c : O, f (omega * c) = f c) :
    ∑ c : O ⧸ Ideal.span {(4 : O)}, f (rep4 c) * cubicTwoChar (rep4 c) = 0 := by
  let F : O ⧸ Ideal.span {(4 : O)} → ℂ := fun c => f (rep4 c) * cubicTwoChar (rep4 c)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) omega) :=
    (omega_primitive.isUnit (by norm_num)).map _
  have hrot : ∀ c, F (hu.unit * c) = cubicTwoChar omega * F c := by
    intro c
    have hcong : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (rep4 (hu.unit * c)) =
        Ideal.Quotient.mk _ (omega * rep4 c) := by
      rw [mk_rep4, map_mul, mk_rep4, IsUnit.unit_spec]
    have h4 : (4 : O) ∣ rep4 (hu.unit * c) - omega * rep4 c :=
      Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hcong)
    have h2 : (2 : O) ∣ rep4 (hu.unit * c) - omega * rep4 c :=
      (show (2 : O) ∣ 4 from ⟨2, by norm_num⟩).trans h4
    change f (rep4 (hu.unit * c)) * cubicTwoChar (rep4 (hu.unit * c)) =
      cubicTwoChar omega * (f (rep4 c) * cubicTwoChar (rep4 c))
    rw [hf4 _ _ hcong, hfω, cubicTwoChar_congr h2, cubicTwoChar_mul]
    ring
  have hS : ∑ c, F c = cubicTwoChar omega * ∑ c, F c := by
    calc ∑ c, F c = ∑ c, F (Units.mulLeft hu.unit c) := (Equiv.sum_comp (Units.mulLeft hu.unit) F).symm
      _ = ∑ c, cubicTwoChar omega * F c := Finset.sum_congr rfl fun c _ => hrot c
      _ = cubicTwoChar omega * ∑ c, F c := (Finset.mul_sum _ _ _).symm
  have h1 : (1 - cubicTwoChar omega) * ∑ c, F c = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm cubicTwoChar_omega_ne_one))

/-- **Column `1`:** the 2-adic phase `Γ(c)(c/−2)₃²` has mean zero modulo `4`. -/
theorem sum_fixedDualAverage_mul_cubicTwoChar :
    ∑ c : O ⧸ Ideal.span {(4 : O)}, fixedDualAverage (rep4 c) * cubicTwoChar (rep4 c) = 0 :=
  sum_mul_cubicTwoChar_eq_zero fixedDualAverage (fixedDualAverage_eq_of_mod_four) fixedDualAverage_omega_mul

/-- **Every column:** the 2-adic phase `\overline{r(n, c)} Γ(c)(c/−2)₃²` of the column `n` has mean zero modulo `4`;
`r(n, c) = Γ(nc)/(Γ(n)Γ(c))` is the quadratic bicharacter of the column law. -/
theorem sum_column_phase_mul_cubicTwoChar (n : O) :
    ∑ c : O ⧸ Ideal.span {(4 : O)}, starRingEnd ℂ (quadraticPhase n (rep4 c)) * fixedDualAverage (rep4 c) *
      cubicTwoChar (rep4 c) = 0 := by
  apply sum_mul_cubicTwoChar_eq_zero (fun c => starRingEnd ℂ (quadraticPhase n c) * fixedDualAverage c)
  · intro c d h
    have hnc : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (n * c) = Ideal.Quotient.mk _ (n * d) := by
      rw [map_mul, map_mul, h]
    simp only [quadraticPhase, fixedDualAverage_eq_of_mod_four _ _ h, fixedDualAverage_eq_of_mod_four _ _ hnc]
  · intro c
    simp only [quadraticPhase, show n * (omega * c) = omega * (n * c) by ring, fixedDualAverage_omega_mul]

/-- **Every layer:** a sixth-power-free row `u = a·b²c³d⁴e⁵` is the squarefree row `a` at the column
`n = b³c²d` times the bicharacter `r(a, M)`, `M = b²c³d⁴e⁵` (`rowConductorGauss_layers`); its 2-adic phase in `a` still
has mean zero modulo `4`. -/
theorem sum_layer_phase_mul_cubicTwoChar (n M : O) :
    ∑ c : O ⧸ Ideal.span {(4 : O)}, quadraticPhase (rep4 c) M * starRingEnd ℂ (quadraticPhase n (rep4 c)) *
      fixedDualAverage (rep4 c) * cubicTwoChar (rep4 c) = 0 := by
  apply sum_mul_cubicTwoChar_eq_zero
    (fun c => quadraticPhase c M * starRingEnd ℂ (quadraticPhase n c) * fixedDualAverage c)
  · intro c d h
    have hcM : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (c * M) = Ideal.Quotient.mk _ (d * M) := by
      rw [map_mul, map_mul, h]
    have hnc : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (n * c) = Ideal.Quotient.mk _ (n * d) := by
      rw [map_mul, map_mul, h]
    simp only [quadraticPhase, fixedDualAverage_eq_of_mod_four _ _ h, fixedDualAverage_eq_of_mod_four _ _ hnc,
      fixedDualAverage_eq_of_mod_four _ _ hcM]
  · intro c
    simp only [quadraticPhase, show n * (omega * c) = omega * (n * c) by ring,
      show omega * c * M = omega * (c * M) by ring, fixedDualAverage_omega_mul]

/-! ### The row root number -/

variable (s : Finset O) (hnz : ∀ π ∈ s, π ≠ 0)
  (hmax : ∀ π ∈ s, (Ideal.span {π}).IsMaximal) (hlam : ∀ π ∈ s, lambda ∉ Ideal.span {π})
  (h2 : ∀ π ∈ s, (2 : O) ∉ Ideal.span {π}) (hprim : ∀ π ∈ s, lambda ^ 2 ∣ π - 1)
  (hcop : (s : Set O).Pairwise IsCoprime) [NeZero (∏ π ∈ s, π)]

include hnz hmax hlam h2 hprim hcop in
/-- **The order-six root number at a squarefree row:** `Φ(c) = Γ(c) χ₂(c) G̃(c)²`. -/
theorem rowRootNumber_eq_weil_mul_cubicTwo :
    sexticGaussPow 1 (∏ π ∈ s, π) 1 / (‖ringComplex (∏ π ∈ s, π)‖ : ℂ) =
      fixedDualAverage (∏ π ∈ s, π) * cubicTwoChar (∏ π ∈ s, π) *
        normalizedCubicUnitGauss (∏ π ∈ s, π) ^ 2 := by
  obtain ⟨hP, hc2⟩ := row_primary s hnz hmax hlam h2 hprim hcop
  rw [rowRootNumber_eq_thetaPhase_mul_gauss_sq s hnz hmax hlam h2 hprim hcop, thetaPhase,
    conj_sexticSymbol_four hP hc2, cubicTwoChar]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
