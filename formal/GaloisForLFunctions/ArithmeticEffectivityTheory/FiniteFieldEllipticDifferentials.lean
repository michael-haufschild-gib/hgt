import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCharts
import Mathlib.RingTheory.Kaehler.Basic
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
/-!
# Genus one from all regular differentials on the finite-field cubic

In the actual function field of `y²=x³−x` over `𝔽₃`, the universal differential
satisfies `dx=y dy`. The dual-number homomorphism `x↦x+εy`, `y↦y+ε` gives a
field derivation taking `y` to one, so `dy` is nonzero.

The affine chart has regular rational differentials `A dy`. On the infinity chart
with `t=x/y`, `u=1/y`, differentiation gives `dt=(1−tu)dy` and `du=−u²dy`.
The identity `(1+tu)dt−t²du=dy` shows its regular differentials are `B dy`.
These are images of the actual Kähler modules, including differentials of every
chart function. The chart overlap agrees after inverting the omitted coordinate.
Since `A∩B=𝔽₃`, the full global regular differential space is `𝔽₃ dy` and has
dimension one.
-/

open Polynomial KaehlerDifferential
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
noncomputable section

abbrev RationalDifferentials := Ω[K⁄Constants]

def dy : RationalDifferentials := D Constants K y

lemma three_eq_zero : (3 : K) = 0 := by
  simpa only [map_natCast, map_ofNat, map_zero, Nat.cast_ofNat] using
    congrArg (algebraMap Constants K) (CharP.cast_eq_zero Constants 3)

/-- The infinitesimal displacement of `x` is `y`. -/

def dualX : TrivSqZeroExt K K := ⟨x, y⟩

/-- The infinitesimal displacement of `y` is one. -/

def dualY : TrivSqZeroExt K K := ⟨y, 1⟩

def coefficientGraph : Constants[X] →+* TrivSqZeroExt K K :=
  Polynomial.eval₂RingHom (algebraMap Constants (TrivSqZeroExt K K)) dualX

lemma coefficientGraph_cubic : coefficientGraph cubic = dualX ^ 3 - dualX := by
  simp [coefficientGraph, cubic]

lemma graph_relation : eval₂ coefficientGraph dualY curve.toAffine.polynomial = 0 := by
  simp only [curve_polynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, coefficientGraph_cubic]
  apply TrivSqZeroExt.ext
  · simpa [dualX, dualY] using sub_eq_zero.mpr relation
  · simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_pow]
    change 2 • (y ^ 1 • (1 : K)) - (3 • (x ^ 2 • y) - y) = 0
    simp only [smul_eq_mul, nsmul_eq_mul, pow_one, mul_one]
    linear_combination (y - x ^ 2 * y) * three_eq_zero

def graph : A →+* TrivSqZeroExt K K := AdjoinRoot.lift coefficientGraph dualY graph_relation

lemma graph_yA : graph yA = dualY := AdjoinRoot.lift_root graph_relation

lemma graph_poly (p : Constants[X]) : graph (algebraMap Constants[X] A p) = coefficientGraph p :=
  AdjoinRoot.lift_of graph_relation

lemma graph_constants (c : Constants) : graph (algebraMap Constants A c) =
    algebraMap Constants (TrivSqZeroExt K K) c := by
  rw [IsScalarTower.algebraMap_apply Constants Constants[X] A, graph_poly]
  simp [coefficientGraph]

def graphAlg : A →ₐ[Constants] TrivSqZeroExt K K :=
  { graph with commutes' := graph_constants }

lemma graph_fst (a : A) : (graph a).fst = algebraMap A K a := by
  have h : (TrivSqZeroExt.fstHom Constants K K).toRingHom.comp graph = algebraMap A K := by
    apply AdjoinRoot.ringHom_ext
    · ext c
      · change (graph (algebraMap Constants A c)).fst =
          algebraMap A K (algebraMap Constants A c)
        rw [graph_constants, ← IsScalarTower.algebraMap_apply Constants A K]
        rfl
      · change (graph (algebraMap Constants[X] A X)).fst = x
        rw [graph_poly]
        simp [coefficientGraph, dualX]
    · change (graph yA).fst = y
      rw [graph_yA]
      rfl
  exact RingHom.congr_fun h a

def affineDerivative : Derivation Constants A K :=
  Derivation.mk'
    (((TrivSqZeroExt.sndHom K K).restrictScalars Constants).comp graphAlg.toLinearMap)
    (by
      intro a b
      change (graph (a * b)).snd = a • (graph b).snd + b • (graph a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, graph_fst, graph_fst]
      simp [Algebra.smul_def, mul_comm])

lemma affineDerivative_yA : affineDerivative yA = 1 := by
  change (graph yA).snd = 1
  rw [graph_yA]
  rfl

/-- The quotient-rule extension of the affine dual-number derivation. -/

def fieldDerivative : Derivation Constants K K := GaloisForLFunctions.fractionRingDerivation affineDerivative

lemma fieldDerivative_y : fieldDerivative y = 1 := by
  change GaloisForLFunctions.fractionRingDerivation affineDerivative (algebraMap A K yA) = 1
  rw [GaloisForLFunctions.fractionRingDerivation_algebraMap, affineDerivative_yA]

/-- The universal differential is nonzero because a field derivation sends it to one. -/

lemma dy_ne_zero : dy ≠ 0 := by
  intro h
  have hh := congrArg fieldDerivative.liftKaehlerDifferential h
  rw [dy, Derivation.liftKaehlerDifferential_comp_D, fieldDerivative_y, map_zero] at hh
  exact one_ne_zero hh

/-- The differential of x is regular even at the ramification points y=0. -/

lemma dx_eq : D Constants K x = y • dy := by
  have h := congrArg (D Constants K) relation
  simp only [map_sub, Derivation.leibniz_pow, show (2 - 1 : ℕ) = 1 by rfl,
    show (3 - 1 : ℕ) = 2 by rfl, pow_one] at h
  rw [← Nat.cast_smul_eq_nsmul K 2, ← Nat.cast_smul_eq_nsmul K 3] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [three_eq_zero, zero_smul, zero_sub] at h
  have ht : (2 : K) = -1 := by linear_combination three_eq_zero
  rw [ht, neg_one_smul] at h
  exact neg_injective h.symm

def t : K := x / y

def u : K := y⁻¹

lemma dt_eq : D Constants K t = (1 - t * u) • dy := by
  rw [t, Derivation.leibniz_div, dx_eq]
  change y⁻¹ ^ 2 • (y • (y • dy) - x • dy) = _
  rw [smul_smul, ← sub_smul, smul_smul]
  congr 1
  dsimp [u]
  field_simp [y_ne_zero]

lemma du_eq : D Constants K u = -u ^ 2 • dy := by
  exact Derivation.leibniz_inv (D Constants K) y

lemma infinity_form_eq :
    (1 + t * u) • D Constants K t - t ^ 2 • D Constants K u = dy := by
  rw [dt_eq, du_eq, smul_smul, smul_smul, ← sub_smul]
  convert one_smul K dy using 1
  congr 1
  ring

lemma dy_coefficient_injective : Function.Injective (fun c : K => c • dy) := by
  intro a b h
  have hh := congrArg fieldDerivative.liftKaehlerDifferential h
  simpa only [map_smul, dy, Derivation.liftKaehlerDifferential_comp_D,
    fieldDerivative_y, smul_eq_mul, mul_one] using hh

lemma aeval_xA (p : Constants[X]) : aeval xA p = algebraMap Constants[X] A p := by
  simpa only [xA, aeval_X_left, AlgHom.id_apply] using
    Polynomial.aeval_algebraMap_apply A (X : Constants[X]) p

lemma aeval_x (p : Constants[X]) : aeval x p = algebraMap A K (algebraMap Constants[X] A p) := by
  rw [x, aeval_algebraMap_apply, aeval_xA]

lemma exists_coordinates (a : A) : ∃ p q : Constants[X],
    algebraMap A K a = aeval x p + aeval x q * y := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  refine ⟨p, q, ?_⟩
  simp only [← yA_eq, Algebra.smul_def, map_add, map_mul, mul_one, aeval_x, y]

lemma x_mem_affine : x ∈ affineChart := ⟨xA, rfl⟩

lemma y_mem_affine : y ∈ affineChart := ⟨yA, rfl⟩

lemma aeval_mem_affine (p : Constants[X]) : aeval x p ∈ affineChart := by
  rw [aeval_x]
  exact ⟨algebraMap Constants[X] A p, rfl⟩

lemma t_mem_infinity : t ∈ infinityChart := Algebra.subset_adjoin (Set.mem_insert _ _)

lemma u_mem_infinity : u ∈ infinityChart := Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

/-- Polynomial evaluation preserves every coefficient subalgebra containing the argument. -/

lemma aeval_mem_chart (B : Subalgebra Constants K) {z : K} (hz : z ∈ B) (p : Constants[X]) :
    aeval z p ∈ B := by
  change aeval (algebraMap B K (⟨z, hz⟩ : B)) p ∈ B
  rw [aeval_algebraMap_apply]
  exact (aeval (⟨z, hz⟩ : B) p).property

/-- The affine chart is generated by the original two coordinate functions. -/

lemma affineChart_eq_adjoin : affineChart = Algebra.adjoin Constants ({x, y} : Set K) := by
  apply le_antisymm
  · rintro z ⟨a, rfl⟩
    obtain ⟨p, q, hpq⟩ := exists_coordinates a
    change algebraMap A K a ∈ _
    rw [hpq]
    have hx : x ∈ Algebra.adjoin Constants ({x, y} : Set K) :=
      Algebra.subset_adjoin (Set.mem_insert _ _)
    have hy : y ∈ Algebra.adjoin Constants ({x, y} : Set K) :=
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    exact (Algebra.adjoin Constants ({x, y} : Set K)).add_mem
      (aeval_mem_chart _ hx p)
      ((Algebra.adjoin Constants ({x, y} : Set K)).mul_mem (aeval_mem_chart _ hx q) hy)
  · apply Algebra.adjoin_le_iff.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact x_mem_affine
    · exact Set.mem_singleton_iff.mp hz ▸ y_mem_affine

/-- Adjoining the inverse of the omitted homogeneous coordinate gives the same overlap on both charts. -/

lemma chart_overlap :
    affineChart ⊔ Algebra.adjoin Constants ({u} : Set K) =
      infinityChart ⊔ Algebra.adjoin Constants ({y} : Set K) := by
  have hleft_y : y ∈ affineChart ⊔ Algebra.adjoin Constants ({u} : Set K) :=
    (le_sup_left : affineChart ≤ _) y_mem_affine
  have hleft_u : u ∈ affineChart ⊔ Algebra.adjoin Constants ({u} : Set K) :=
    (le_sup_right : Algebra.adjoin Constants ({u} : Set K) ≤ _)
      (Algebra.subset_adjoin rfl)
  have hright_t : t ∈ infinityChart ⊔ Algebra.adjoin Constants ({y} : Set K) :=
    (le_sup_left : infinityChart ≤ _) t_mem_infinity
  have hright_u : u ∈ infinityChart ⊔ Algebra.adjoin Constants ({y} : Set K) :=
    (le_sup_left : infinityChart ≤ _) u_mem_infinity
  have hright_y : y ∈ infinityChart ⊔ Algebra.adjoin Constants ({y} : Set K) :=
    (le_sup_right : Algebra.adjoin Constants ({y} : Set K) ≤ _)
      (Algebra.subset_adjoin rfl)
  have hx : x = t * y := by dsimp [t]; field_simp [y_ne_zero]
  have ht : t = x * u := div_eq_mul_inv x y
  apply le_antisymm
  · apply sup_le
    · rw [affineChart_eq_adjoin]
      apply Algebra.adjoin_le_iff.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · rw [hx]
        exact (infinityChart ⊔ Algebra.adjoin Constants ({y} : Set K)).mul_mem hright_t hright_y
      · exact Set.mem_singleton_iff.mp hz ▸ hright_y
    · exact Algebra.adjoin_le_iff.mpr (by rintro z rfl; exact hright_u)
  · apply sup_le
    · apply Algebra.adjoin_le_iff.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · change t ∈ _
        rw [ht]
        exact (affineChart ⊔ Algebra.adjoin Constants ({u} : Set K)).mul_mem
          ((le_sup_left : affineChart ≤ _) x_mem_affine) hleft_u
      · exact Set.mem_singleton_iff.mp hz ▸ hleft_u
    · exact Algebra.adjoin_le_iff.mpr (by rintro z rfl; exact hleft_y)

/-- Regular rational differentials on an affine chart are the image of its universal differentials. -/

def chartForms (B : Subalgebra Constants K) : Submodule Constants RationalDifferentials :=
  (LinearMap.range (KaehlerDifferential.map Constants Constants B K)).restrictScalars Constants

/-- The same image is generated over the chart ring by all differentials of chart functions. -/

lemma chartForms_eq_span (B : Subalgebra Constants K) :
    chartForms B = (Submodule.span B (Set.range fun b : B => D Constants K (b : K))).restrictScalars Constants := by
  unfold chartForms
  apply congrArg (fun N : Submodule B RationalDifferentials => N.restrictScalars Constants)
  rw [← Submodule.map_top, ← KaehlerDifferential.span_range_derivation Constants B,
    Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span B)
  apply congrArg Set.range
  funext b
  exact KaehlerDifferential.map_D Constants Constants B K b

/-- Coefficients in a chart multiplying the common invariant form. -/

def chartLine (B : Subalgebra Constants K) : Submodule B RationalDifferentials := Submodule.span B {dy}

lemma chartLine_dy (B : Subalgebra Constants K) : dy ∈ chartLine B :=
  Submodule.subset_span rfl

lemma chartForms_eq_line (B : Subalgebra Constants K)
    (hD : ∀ b : B, D Constants K (b : K) ∈ chartLine B)
    (hdy : dy ∈ Submodule.span B (Set.range fun b : B => D Constants K (b : K))) :
    chartForms B = (chartLine B).restrictScalars Constants := by
  rw [chartForms_eq_span]
  apply congrArg (fun N : Submodule B RationalDifferentials => N.restrictScalars Constants)
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hD b)
  · exact Submodule.span_le.mpr (by rintro z rfl; exact hdy)

lemma affine_derivatives_in_line (a : affineChart) :
    D Constants K (a : K) ∈ chartLine affineChart := by
  have hdx : D Constants K x ∈ chartLine affineChart := by
    rw [dx_eq]
    exact (chartLine affineChart).smul_mem ⟨y, y_mem_affine⟩ (chartLine_dy _)
  have hpoly (p : Constants[X]) : D Constants K (aeval x p) ∈ chartLine affineChart := by
    rw [Derivation.map_aeval]
    exact (chartLine affineChart).smul_mem ⟨aeval x p.derivative, aeval_mem_affine _⟩ hdx
  obtain ⟨aA, ha⟩ := a.property
  obtain ⟨p, q, hpq⟩ := exists_coordinates aA
  have heq : (a : K) = aeval x p + aeval x q * y := ha.symm.trans hpq
  rw [heq, map_add, Derivation.leibniz]
  exact (chartLine affineChart).add_mem (hpoly p)
    ((chartLine affineChart).add_mem
      ((chartLine affineChart).smul_mem ⟨aeval x q, aeval_mem_affine q⟩ (chartLine_dy _))
      ((chartLine affineChart).smul_mem ⟨y, y_mem_affine⟩ (hpoly q)))

/-- Every regular affine differential is an affine coefficient times `dy`. -/

lemma affineForms_eq_line : chartForms affineChart = (chartLine affineChart).restrictScalars Constants :=
  chartForms_eq_line _ affine_derivatives_in_line
    (Submodule.subset_span ⟨⟨y, y_mem_affine⟩, rfl⟩)

lemma infinity_derivatives_in_line (a : infinityChart) :
    D Constants K (a : K) ∈ chartLine infinityChart := by
  refine Algebra.adjoin_induction (p := fun z _ => D Constants K z ∈ chartLine infinityChart)
    ?_ ?_ ?_ ?_ a.property
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · rw [show x / y = t from rfl, dt_eq]
      exact (chartLine infinityChart).smul_mem
        ⟨1 - t * u, infinityChart.sub_mem infinityChart.one_mem
          (infinityChart.mul_mem t_mem_infinity u_mem_infinity)⟩ (chartLine_dy _)
    · rcases Set.mem_singleton_iff.mp hz with rfl
      rw [show y⁻¹ = u from rfl, du_eq]
      exact (chartLine infinityChart).smul_mem
        ⟨-u ^ 2, infinityChart.neg_mem (infinityChart.pow_mem u_mem_infinity 2)⟩ (chartLine_dy _)
  · intro c
    rw [Derivation.map_algebraMap]
    exact (chartLine infinityChart).zero_mem
  · intro z w hz hw hDz hDw
    rw [map_add]
    exact (chartLine infinityChart).add_mem hDz hDw
  · intro z w hz hw hDz hDw
    rw [Derivation.leibniz]
    exact (chartLine infinityChart).add_mem
      ((chartLine infinityChart).smul_mem ⟨z, hz⟩ hDw)
      ((chartLine infinityChart).smul_mem ⟨w, hw⟩ hDz)

lemma dy_mem_infinity_span :
    dy ∈ Submodule.span infinityChart (Set.range fun b : infinityChart => D Constants K (b : K)) := by
  have ht : D Constants K t ∈ Submodule.span infinityChart
      (Set.range fun b : infinityChart => D Constants K (b : K)) :=
    Submodule.subset_span ⟨⟨t, t_mem_infinity⟩, rfl⟩
  have hu : D Constants K u ∈ Submodule.span infinityChart
      (Set.range fun b : infinityChart => D Constants K (b : K)) :=
    Submodule.subset_span ⟨⟨u, u_mem_infinity⟩, rfl⟩
  have hh := (Submodule.span infinityChart
      (Set.range fun b : infinityChart => D Constants K (b : K))).sub_mem
    (Submodule.smul_mem _
      (⟨1 + t * u, infinityChart.add_mem infinityChart.one_mem
        (infinityChart.mul_mem t_mem_infinity u_mem_infinity)⟩ : infinityChart) ht)
    (Submodule.smul_mem _
      (⟨t ^ 2, infinityChart.pow_mem t_mem_infinity 2⟩ : infinityChart) hu)
  change (1 + t * u) • D Constants K t - t ^ 2 • D Constants K u ∈ _ at hh
  rwa [infinity_form_eq] at hh

/-- The invariant differential is also a generator on the chart containing infinity. -/

lemma infinityForms_eq_line :
    chartForms infinityChart = (chartLine infinityChart).restrictScalars Constants :=
  chartForms_eq_line _ infinity_derivatives_in_line dy_mem_infinity_span

/-- Rational differentials regular on both charts of the smooth projective cubic. -/

def regularForms : Submodule Constants RationalDifferentials :=
  chartForms affineChart ⊓ chartForms infinityChart

lemma dy_mem_regularForms : dy ∈ regularForms := by
  constructor
  · rw [affineForms_eq_line]
    exact chartLine_dy _
  · rw [infinityForms_eq_line]
    exact chartLine_dy _

/-- The full space of globally regular differentials consists exactly of constant multiples of `dy`. -/

lemma regularForms_eq_span : regularForms = Submodule.span Constants {dy} := by
  apply le_antisymm
  · intro ω hω
    obtain ⟨hA, hB⟩ := hω
    rw [affineForms_eq_line] at hA
    rw [infinityForms_eq_line] at hB
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hA
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hB
    have hab : (a : K) = (b : K) := dy_coefficient_injective (ha.trans hb.symm)
    obtain ⟨c, hc⟩ := (mem_both_charts_iff (a : K)).mp
      ⟨a.property, hab.symm ▸ b.property⟩
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [← IsScalarTower.algebraMap_smul K, ← hc]
    exact ha
  · exact Submodule.span_le.mpr (by rintro ω rfl; exact dy_mem_regularForms)

/-- Geometric genus, defined by all globally regular rational one-forms. -/

def geometricGenus : ℕ := Module.finrank Constants regularForms

lemma geometricGenus_eq_one : geometricGenus = 1 := by
  rw [geometricGenus, regularForms_eq_span]
  exact finrank_span_singleton dy_ne_zero

lemma geometricGenus_pos : 0 < geometricGenus := by
  rw [geometricGenus_eq_one]
  exact Nat.zero_lt_one
end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
