import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.ShortColumnsOfTheEisensteinLatticeAreIncoherent
import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGaussSumsAreTwistedMultiplicative

/-!
# The Gram entry of two rows is a completed sum with its own reflection

The off-diagonal entry of the signed Gram of the sextic family is a column sum
`G(u₁, u₂) = Σ_{n ∈ ℤ[ω]} χ_{u₁}(n) χ_{u₂}(n)⁵ f(Bn)` of the product of two residue symbols over
rows weighted by a smooth profile. This module evaluates it exactly.

* `tsum_column_eq_dual` (**reflection of a column**): for any function `φ` on `O/(c)`,
  `Σ_n φ(n) f(Bn) = |O/(c)|⁻¹ |det B|⁻¹ Σ_{h mod c} φ̂(h) Σ_m f̂(B^{−*}(m − θ_h))`, with
  `φ̂(h) = Σ_d φ(d) ψ_c(−hd)` and the dual frequency `θ_h` of `ψ_c(h·)`.
* `sum_pairColumn_traceChar` (**the mixed Gauss sum splits**): for coprime `c, d`,
  `Σ_{m mod cd} χ_c(m)^i χ_d(m)^j ψ_{cd}(hm) = χ_c(d)^i χ_d(c)^j g_c^{(i)}(h) g_d^{(j)}(h)`.
* `gramEntry_eq_completedSum`: hence
  `G(u₁, u₂) = |O/(u₁u₂)|⁻¹ |det B|⁻¹ χ_{u₁}(u₂) χ_{u₂}(u₁)⁵ Σ_h g_{u₁}^{(1)}(−h) g_{u₂}^{(5)}(−h) ·
  Σ_m f̂(B^{−*}(m − θ_h))`.

The pair of rows is a completed sum over the dual frequencies `h mod u₁u₂` whose amplitudes are
the products of the two rows' Gauss sums, twisted by the reciprocity factor `χ_{u₁}(u₂)χ_{u₂}(u₁)⁵`
(a quadratic phase by sextic reciprocity), and whose length is the dual length of the column:
every `h ≢ 0` sits at distance `≥ √(2/(3N(u₁u₂)))` from the lattice
(`sqrt_le_norm_sub_thetaH`). Its own reflection is the same formula read from the dual side.
-/

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open HTGeometry HTGeometry.IntegerLatticePoisson MetaplecticMobiusDescent
  MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates
  FamilyContinuationTheory

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Z" => Fin 2 → ℤ

/-! ### The reflection of a column -/

/-- The chosen representative of a residue class. -/
def repr {c : O} (h : O ⧸ Ideal.span {c}) : O := Classical.choose (Ideal.Quotient.mk_surjective h)

theorem mk_repr {c : O} (h : O ⧸ Ideal.span {c}) : Ideal.Quotient.mk _ (repr h) = h :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective h)

/-- The dual frequency of the class `h`. -/
def dualFreq (a b : ℤ) {c : O} (h : O ⧸ Ideal.span {c}) : E :=
  thetaH a b (coords (repr h)).1 (coords (repr h)).2

/-- The dual coefficient `φ̂(h) = Σ_d φ(d) ψ_c(−hd)`. -/
def dualCoeff (a b : ℤ) [hc : NeZero (eval a b)] (φ : O ⧸ Ideal.span {eval a b} → ℂ)
    (h : O ⧸ Ideal.span {eval a b}) : ℂ :=
  ∑ d, φ d * principalTraceChar (eval a b) hc.ne (-(h * d))

/-- **The reflection of a column.** For any function `φ` on `O/(c)`, `c = a + bω ≠ 0`, and rows
weighted by a Schwartz profile `f(Bn)`:
`Σ_n φ(n mod c) f(Bn) = |O/(c)|⁻¹ |det B|⁻¹ Σ_h φ̂(h) Σ_m f̂(B^{−*}(m − θ_h))`. -/
theorem tsum_column_eq_dual (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (a b : ℤ)
    [hc : NeZero (eval a b)] (φ : O ⧸ Ideal.span {eval a b} → ℂ) :
    ∑' n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) * f (B (euclideanIntegerPoint n)) =
      ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * (latticeScale B : ℂ) *
        ∑ h, dualCoeff a b φ h *
          ∑' m : Z, (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - dualFreq a b h)) := by
  have hc0 : eval a b ≠ 0 := hc.ne
  set ψ := principalTraceChar (eval a b) hc0
  have hψ : ψ.IsPrimitive := principalTraceChar_primitive _ hc0
  have hcard : ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := O ⧸ Ideal.span {eval a b})).ne'
  -- each class is a lattice phase
  have hphase : ∀ (h : O ⧸ Ideal.span {eval a b}) (n : Z),
      ψ (h * Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
        phase (dualFreq a b h) (euclideanIntegerPoint n) := by
    intro h n
    have hh : h = Ideal.Quotient.mk _ (eval (coords (repr h)).1 (coords (repr h)).2) := by
      rw [eval_coords, mk_repr]
    conv_lhs => rw [hh, ← map_mul]
    exact traceChar_mul_eval_eq_phase a b _ _ hc0 n
  -- the column as a finite combination of phases
  have hexp : ∀ n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
      ∑ h, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * dualCoeff a b φ h) *
        phase (dualFreq a b h) (euclideanIntegerPoint n) := by
    intro n
    have hinv := card_mul_eq_sum_dual hψ φ (Ideal.Quotient.mk _ (eval (n 0) (n 1)))
    calc φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) =
          ((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ *
            (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ)) *
              φ (Ideal.Quotient.mk _ (eval (n 0) (n 1)))) := by field_simp
      _ = _ := by
          rw [hinv, Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hphase]
          unfold dualCoeff
          ring
  have hsumf : ∀ h : O ⧸ Ideal.span {eval a b}, Summable fun n : Z =>
      phase (dualFreq a b h) (euclideanIntegerPoint n) * f (B (euclideanIntegerPoint n)) := by
    intro h
    refine Summable.of_norm ?_
    refine (summable_norm_affine_lattice f B 0).congr fun n => ?_
    rw [norm_mul, norm_phase, one_mul, add_zero]
  calc ∑' n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) * f (B (euclideanIntegerPoint n)) =
        ∑' n : Z, ∑ h, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ *
          dualCoeff a b φ h) * (phase (dualFreq a b h) (euclideanIntegerPoint n) *
            f (B (euclideanIntegerPoint n))) := by
        congr 1
        funext n
        rw [hexp n, Finset.sum_mul]
        refine Finset.sum_congr rfl fun h _ => by ring
    _ = ∑ h, (((Fintype.card (O ⧸ Ideal.span {eval a b}) : ℂ))⁻¹ * dualCoeff a b φ h) *
          ∑' n : Z, phase (dualFreq a b h) (euclideanIntegerPoint n) *
            f (B (euclideanIntegerPoint n)) := by
        rw [Summable.tsum_finsetSum fun h _ => (hsumf h).mul_left _]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [tsum_mul_left]
    _ = _ := by
        simp_rw [tsum_phase_mul_comp_eq]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => by ring

/-- The dual frequency of the class `h` for a modulus `c`, in the coordinates of `c`. -/
def dualFreqOf (c : O) (h : O ⧸ Ideal.span {c}) : E :=
  thetaH (coords c).1 (coords c).2 (coords (repr h)).1 (coords (repr h)).2

/-- The dual coefficient for a modulus `c`. -/
def dualCoeffOf (c : O) [hc : NeZero c] (φ : O ⧸ Ideal.span {c} → ℂ) (h : O ⧸ Ideal.span {c}) :
    ℂ :=
  ∑ d, φ d * principalTraceChar c hc.ne (-(h * d))

/-- **The reflection of a column**, for any nonzero modulus `c`. -/
theorem tsum_column_eq_dualOf (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (c : O) [hc : NeZero c]
    (φ : O ⧸ Ideal.span {c} → ℂ) :
    ∑' n : Z, φ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) * f (B (euclideanIntegerPoint n)) =
      ((Fintype.card (O ⧸ Ideal.span {c}) : ℂ))⁻¹ * (latticeScale B : ℂ) *
        ∑ h, dualCoeffOf c φ h *
          ∑' m : Z, (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - dualFreqOf c h)) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℤ, eval a b = c := ⟨_, _, eval_coords c⟩
  have hab : coords (eval a b) = (a, b) := coords_eval a b
  have h := tsum_column_eq_dual f B a b φ
  rw [h]
  unfold dualFreqOf dualFreq dualCoeffOf dualCoeff
  rw [hab]

/-! ### The mixed Gauss sum of a pair of rows -/

/-- The pair column `m ↦ χ_c(m)^i χ_d(m)^j` on `O/(cd)`. -/
def pairColumn (i j : ℕ) (c d : O) (m : O ⧸ Ideal.span {c * d}) : ℂ :=
  sexticResidue c (reduceLeft c d m) ^ i * sexticResidue d (reduceRight c d m) ^ j

theorem pairColumn_mk (i j : ℕ) (c d x : O) :
    pairColumn i j c d (Ideal.Quotient.mk _ x) = sexticSymbol x c ^ i * sexticSymbol x d ^ j := by
  simp only [pairColumn, reduceLeft, reduceRight, Ideal.Quotient.factor_mk, sexticResidue_mk]

/-- **The mixed Gauss sum splits.** For coprime `c, d`:
`Σ_{m mod cd} χ_c(m)^i χ_d(m)^j ψ_{cd}(hm) = χ_c(d)^i χ_d(c)^j g_c^{(i)}(h) g_d^{(j)}(h)`. -/
theorem sum_pairColumn_traceChar (i j : ℕ) (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d)
    (h : O) :
    ∑ m : O ⧸ Ideal.span {c * d}, pairColumn i j c d m *
        principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
          (Ideal.Quotient.mk _ h * m) =
      sexticSymbol d c ^ i * sexticSymbol c d ^ j * sexticGaussPow i c h * sexticGaussPow j d h := by
  unfold pairColumn
  rw [sum_crt_mul_traceChar c d hcd (fun x => sexticResidue c x ^ i)
    (fun y => sexticResidue d y ^ j)]
  have hx : ∀ x : O ⧸ Ideal.span {c},
      sexticResidue c (Ideal.Quotient.mk _ d * x) ^ i =
        sexticSymbol d c ^ i * sexticResidue c x ^ i := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, sexticResidue_mk, sexticResidue_mk, sexticSymbol_mul_numerator, mul_pow]
  have hy : ∀ y : O ⧸ Ideal.span {d},
      sexticResidue d (Ideal.Quotient.mk _ c * y) ^ j =
        sexticSymbol c d ^ j * sexticResidue d y ^ j := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, sexticResidue_mk, sexticResidue_mk, sexticSymbol_mul_numerator, mul_pow]
  simp only [hx, hy, mul_assoc, ← Finset.mul_sum]
  unfold sexticGaussPow
  ring

/-! ### The Gram entry -/

/-- **The Gram entry of two rows is a completed sum.** For coprime nonzero moduli `u₁, u₂`, the
column sum of `χ_{u₁}χ_{u₂}⁵` over rows weighted by `f(Bn)` is
`|O/(u₁u₂)|⁻¹ |det B|⁻¹ χ_{u₁}(u₂)χ_{u₂}(u₁)⁵ Σ_{h mod u₁u₂} g_{u₁}^{(1)}(−h) g_{u₂}^{(5)}(−h)
Σ_m f̂(B^{−*}(m − θ_h))`. -/
theorem gramEntry_eq_completedSum (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (u₁ u₂ : O)
    [NeZero u₁] [NeZero u₂] (hcop : IsCoprime u₁ u₂) [NeZero (u₁ * u₂)] :
    ∑' n : Z, (sexticSymbol (eval (n 0) (n 1)) u₁ * sexticSymbol (eval (n 0) (n 1)) u₂ ^ 5) *
        f (B (euclideanIntegerPoint n)) =
      ((Fintype.card (O ⧸ Ideal.span {u₁ * u₂}) : ℂ))⁻¹ * (latticeScale B : ℂ) *
        ∑ h : O ⧸ Ideal.span {u₁ * u₂},
          (sexticSymbol u₂ u₁ * sexticSymbol u₁ u₂ ^ 5 *
            sexticGaussPow 1 u₁ (-(repr h)) * sexticGaussPow 5 u₂ (-(repr h))) *
          ∑' m : Z, (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - dualFreqOf (u₁ * u₂) h)) := by
  have hcol : ∀ n : Z, sexticSymbol (eval (n 0) (n 1)) u₁ * sexticSymbol (eval (n 0) (n 1)) u₂ ^ 5 =
      pairColumn 1 5 u₁ u₂ (Ideal.Quotient.mk _ (eval (n 0) (n 1))) := by
    intro n
    rw [pairColumn_mk, pow_one]
  simp_rw [hcol]
  rw [tsum_column_eq_dualOf f B (u₁ * u₂) (pairColumn 1 5 u₁ u₂)]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  congr 1
  unfold dualCoeffOf
  have hneg : ∀ d : O ⧸ Ideal.span {u₁ * u₂}, -(h * d) = Ideal.Quotient.mk _ (-(repr h)) * d := by
    intro d
    rw [map_neg, mk_repr, neg_mul]
  simp_rw [hneg]
  rw [sum_pairColumn_traceChar 1 5 u₁ u₂ hcop (-(repr h)), pow_one]

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
