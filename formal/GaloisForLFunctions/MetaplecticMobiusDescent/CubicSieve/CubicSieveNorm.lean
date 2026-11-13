/-
The cubic sieve norm adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.PrimeFamiliesAndIdealCounts

/-!
# The cubic sieve norm

Admissible ideals, cubic rows and the sieve norm `CubicSieve.sieveNorm` with the cubic exponent
condition `HasCubicExponent`; the native prime-row estimate gives the initial exponent two;
GCD Möbius descent.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CubicSieve
/-- Squarefree ideals with a nonzero primary generator. -/
def Admissible (I : Ideal Eis) : Prop := Squarefree I ∧ primaryIdealGenerator I ≠ 0

def idealKernel (I J : Ideal Eis) : ℂ :=
  ringComplex (idealSymbol I (primaryIdealGenerator J))

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I := by
  apply congrArg ringComplex
  have he := symbol_reciprocity (primaryIdealGenerator J) (primaryIdealGenerator I)
    (primaryIdealGenerator_spec J hJ).2 (primaryIdealGenerator_spec I hI).2
  simpa only [symbol,(primaryIdealGenerator_spec I hI).1,
    (primaryIdealGenerator_spec J hJ).1] using he

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ←idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (idealRowHom_norm (primaryIdealGenerator J) I) 2).trans_eq
    (by norm_num)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (ringComplex (idealSymbol I x)) ^ 4 = ringComplex (idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (ringComplex (primeValue P x)) ^ 4 = ringComplex (primeValue P x) := by
    by_cases h : P.IsMaximal ∧ lambda ∉ P
    · letI : P.IsMaximal := h.1
      have hχ : (complexSexticChar P h.2 ^ 2) ^ 3 = 1 := by
        rw [←pow_mul]
        exact (complexSexticChar_powers P h.2).2.2
      rw [←localRowValue_square,localRowValue_good x P h.2]
      simpa only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)] using
        cubic_fourth_eq (complexSexticChar P h.2 ^ 2) hχ (Ideal.Quotient.mk P x)
    · simp only [primeValue,dif_neg h,map_zero,zero_pow (by decide : (4:ℕ) ≠ 0)]
  have hprod (S : Multiset (Ideal Eis)) :
      (ringComplex ((S.map (fun P => primeValue P x)).prod)) ^ 4 =
        ringComplex ((S.map (fun P => primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,mul_pow,hlocal,ih]
  by_cases hI : I = 0
  · simp only [hI,idealSymbol_zero,map_zero,zero_pow (by decide : (4:ℕ) ≠ 0)]
  · simpa only [idealSymbol,if_neg hI] using hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealSymbol_cube_mask (I : Ideal Eis) (x : Eis)
    (hI : primaryIdealGenerator I ≠ 0) :
    (ringComplex (idealSymbol I x)) ^ 3 = if IsCoprime I (Ideal.span {x}) then 1 else 0 := by
  have hlocal (P : Ideal Eis) (hP : P.IsMaximal ∧ lambda ∉ P) :
      (ringComplex (primeValue P x)) ^ 3 = if IsCoprime P (Ideal.span {x}) then 1 else 0 := by
    letI : P.IsMaximal := hP.1
    rw [←localRowValue_square,localRowValue_good x P hP.2,←pow_mul]
    have he := idealRowHom_prime_sixth_mask x P hP.2
    rw [idealRowHom_prime _ P hP.2,map_pow,map_pow] at he
    exact he
  have hprod (S : Multiset (Ideal Eis))
      (hS : ∀ P ∈ S, P.IsMaximal ∧ lambda ∉ P) :
      (ringComplex ((S.map (fun P => primeValue P x)).prod)) ^ 3 =
        if IsCoprime S.prod (Ideal.span {x}) then 1 else 0 := by
    induction S using Multiset.induction_on with
    | empty => simp only [Multiset.map_zero,Multiset.prod_zero,map_one,one_pow,isCoprime_one_left,ite_true]
    | @cons P S ih =>
      have hp := hS P (Multiset.mem_cons_self _ _)
      have ht := fun Q hQ => hS Q (Multiset.mem_cons_of_mem hQ)
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,mul_pow,hlocal P hp,ih ht,IsCoprime.mul_left_iff]
      by_cases hP : IsCoprime P (Ideal.span {x}) <;>
        by_cases hS : IsCoprime S.prod (Ideal.span {x}) <;> simp [hP,hS]
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, P.IsMaximal ∧ lambda ∉ P := by
    intro P hP
    have h := primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P hI hP)
    exact ⟨h.1,h.2.1⟩
  have h := hprod (UniqueFactorizationMonoid.normalizedFactors I) hf
  rw [Ideal.prod_normalizedFactors_eq_self hI0] at h
  simpa only [idealSymbol,if_neg hI0] using h

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryIdealGenerator J))

def idealNumeratorHom (I : Ideal Eis) (hI : primaryIdealGenerator I ≠ 0) : Ideal Eis →* ℂ where
  toFun := idealKernel I
  map_one' := by
    rw [idealKernel,primaryIdealGenerator_one,←idealRowHom_square,idealRowHom_one_good I hI,one_pow]
  map_mul' A B := by
    simp only [idealKernel,primaryIdealGenerator_mul,idealSymbol_map_mul,map_mul]

theorem idealKernel_row_decomposition (I A B C : Ideal Eis) (hI : primaryIdealGenerator I ≠ 0) :
    idealKernel I (A * B ^ 2 * C ^ 3) =
      idealKernel I A * star (idealKernel I B) * idealKernel I C ^ 3 := by
  change idealNumeratorHom I hI (A * B ^ 2 * C ^ 3) = _
  rw [map_mul,map_mul,map_pow,map_pow]
  change idealKernel I A * idealKernel I B ^ 2 * idealKernel I C ^ 3 = _
  rw [idealKernel_square_eq_star]

end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion FiniteSieveOperator
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CubicSieve
/-- Squarefree primary ideals of bounded norm. -/
def idealRange (X : ℝ) : Finset (Ideal Eis) :=
  (Ideal.finite_setOf_absNorm_le (S := Eis) ⌈max 0 X⌉₊).toFinset.filter
    (fun I => Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X)

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    rw [Set.Finite.mem_toFinset]
    exact Nat.cast_le.mp (h.2.trans ((le_max_right 0 X).trans (Nat.le_ceil _)))

def idealMatrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => idealKernel J.val I.val

def sieveNorm (M N : ℝ) : ℝ := squaredNorm (idealMatrix M N)

theorem sieveNorm_reciprocity (M N : ℝ) : sieveNorm M N = sieveNorm N M := by
  apply squaredNorm_reciprocity
  intro I J
  exact idealKernel_reciprocity J.val I.val
    (mem_idealRange.mp J.property).1.2 (mem_idealRange.mp I.property).1.2

theorem ideal_energy_bound (M N : ℝ) (coef : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      idealKernel J.val I.val * coef J‖ ^ 2) ≤
        sieveNorm M N * ∑ J, ‖coef J‖ ^ 2 :=
  energy_le_squaredNorm (idealMatrix M N) coef

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem ideal_cube_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal Eis) (B : b → Ideal Eis) (C : c → Ideal Eis)
    (cols : n → Ideal Eis) (hc : ∀ j, primaryIdealGenerator (cols j) ≠ 0)
    (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j *
      idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)) =
        ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
          coef j * idealKernel (cols j) (C l) ^ 3 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [idealKernel_row_decomposition _ _ _ _ (hc j)]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · intro l j
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (idealKernel_norm_le_one _ _) 3).trans_eq (by norm_num)

theorem ideal_cubic_factorization (I : Ideal Eis) (hI : I ≠ 0) :
    I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI

end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace CubicSieve

abbrev CubicPrime := {P : Ideal O // P.IsMaximal ∧ lambda ∉ P}
instance cubicPrimeMaximal (P : CubicPrime) : P.val.IsMaximal := P.property.1

def primeGenerator (P : CubicPrime) : O := primaryIdealPrime P.val
lemma primeGenerator_ne_zero (P : CubicPrime) : primeGenerator P ≠ 0 :=
  primaryIdealPrime_ne_zero P.val P.property.2
lemma primeGenerator_span (P : CubicPrime) : Ideal.span {primeGenerator P} = P.val :=
  (primaryIdealPrime_spec P.val (primeGenerator_ne_zero P)).2.2.1
instance primeGeneratorMaximal (P : CubicPrime) : (Ideal.span {primeGenerator P}).IsMaximal := by
  rw [primeGenerator_span]
  infer_instance
lemma primeGenerator_good (P : CubicPrime) : lambda ∉ Ideal.span {primeGenerator P} := by
  rw [primeGenerator_span]
  exact P.property.2
lemma primeGenerator_span_injective :
    Function.Injective (fun P : CubicPrime => Ideal.span {primeGenerator P}) := by
  intro P Q h
  exact Subtype.ext (by simpa only [primeGenerator_span] using h)

abbrev CubicIdeal := {I : Ideal O // Admissible I}
def idealPrimeIndex (I : CubicIdeal) (P : primeSupport I.val) : CubicPrime :=
  ⟨P.val, (primaryIdealPrime_spec P.val
    (primaryIdealPrime_factor_ne_zero I.val P.val I.property.2
      (Multiset.mem_toFinset.mp P.property))).1,
    (primaryIdealPrime_spec P.val
    (primaryIdealPrime_factor_ne_zero I.val P.val I.property.2
      (Multiset.mem_toFinset.mp P.property))).2.1⟩

def idealSupport (I : CubicIdeal) : Finset CubicPrime :=
  (primeSupport I.val).attach.map
    ⟨idealPrimeIndex I, fun _ _ h => Subtype.ext (congrArg (fun P : CubicPrime => P.val) h)⟩

lemma idealSupport_product (I : CubicIdeal) :
    (∏ P ∈ idealSupport I, primeGenerator P) = primaryIdealGenerator I.val := by
  rw [idealSupport, Finset.prod_map]
  change (∏ P ∈ (primeSupport I.val).attach, primaryIdealPrime P.val) = _
  rw [Finset.prod_attach]
  exact (primaryIdealGenerator_squarefree_support I.val I.property.2 I.property.1).symm

lemma idealSupport_ideal_product (I : CubicIdeal) :
    (∏ P ∈ idealSupport I, P.val) = I.val := by
  rw [idealSupport, Finset.prod_map]
  change (∏ P ∈ (primeSupport I.val).attach, P.val) = _
  rw [Finset.prod_attach (primeSupport I.val) (fun P : Ideal O => P)]
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    (primaryIdealGenerator_ne_zero_ideal I.val I.property.2)).mp I.property.1
  have hv : (primeSupport I.val).val = UniqueFactorizationMonoid.normalizedFactors I.val := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  change (primeSupport I.val).prod id = I.val
  rw [←Finset.prod_val, hv]
  exact Ideal.prod_normalizedFactors_eq_self (primaryIdealGenerator_ne_zero_ideal I.val I.property.2)

lemma idealGenerator_injective :
    Function.Injective (fun I : CubicIdeal => primaryIdealGenerator I.val) := by
  intro I J h
  change primaryIdealGenerator I.val = primaryIdealGenerator J.val at h
  apply Subtype.ext
  rw [←(primaryIdealGenerator_spec I.val I.property.2).1,
    ←(primaryIdealGenerator_spec J.val J.property.2).1, h]

lemma idealSupport_injective : Function.Injective idealSupport := by
  intro I J h
  apply idealGenerator_injective
  change primaryIdealGenerator I.val = primaryIdealGenerator J.val
  rw [←idealSupport_product I, ←idealSupport_product J, h]

lemma idealSupport_norm (I : CubicIdeal) :
    primeSubsetNorm primeGenerator (idealSupport I) = (Ideal.absNorm I.val : ℝ) := by
  rw [primeSubsetNorm, idealSupport_product, primaryIdealGenerator_norm_sq I.val I.property.2]

lemma idealSymbol_eq_primeSubsetRow (I : CubicIdeal) (z : O) :
    ringComplex (idealSymbol I.val z) = primeSubsetRow primeGenerator
      (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
      (idealSupport I) z := by
  rw [←idealRowHom_square, ←idealSupport_ideal_product I, map_prod,
    ←Finset.prod_pow]
  unfold primeSubsetRow
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime _ P.val P.property.2,
    ←MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), (complexSexticChar_powers P.val P.property.2).1]
  change ringComplex (cubicChar P.val P.property.2 (Ideal.Quotient.mk P.val z)) =
    ringComplex (cubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P)
      (Ideal.Quotient.mk (Ideal.span {primeGenerator P}) z))
  rw [←primeValue_eq P.val P.property.2,
    ←primeValue_eq (Ideal.span {primeGenerator P}) (primeGenerator_good P),primeGenerator_span]

/-- The native prime-row estimate gives the initial cubic exponent two. -/
theorem sieveNorm_initial : ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M + N ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := primeSubsetRow_initial_operator_bound
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  let rows : idealRange M → CubicIdeal := fun I => ⟨I.val, (mem_idealRange.mp I.property).1⟩
  let cols : idealRange N → CubicIdeal := fun I => ⟨I.val, (mem_idealRange.mp I.property).1⟩
  have hr : Function.Injective rows := fun I J h => Subtype.ext (congrArg (fun I : CubicIdeal => I.val) h)
  have hc : Function.Injective cols := fun I J h => Subtype.ext (congrArg (fun I : CubicIdeal => I.val) h)
  have hb := hbound primeGenerator primeGenerator_ne_zero primeGenerator_span_injective
    (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
    (fun P => complexCubicChar_ne_one _ (primeGenerator_good P))
    (fun I => primaryIdealGenerator (rows I).val) (idealGenerator_injective.comp hr)
    (fun J => idealSupport (cols J)) (idealSupport_injective.comp hc) M N hM hN
    (fun I => by
      rw [primaryIdealGenerator_norm_sq _ (rows I).property.2]
      exact (mem_idealRange.mp I.property).2)
    (fun J => by rw [idealSupport_norm]; exact (mem_idealRange.mp J.property).2)
  have he : idealMatrix M N = fun I J => primeSubsetRow primeGenerator
      (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
      (idealSupport (cols J)) (primaryIdealGenerator (rows I).val) := by
    ext I J
    exact idealSymbol_eq_primeSubsetRow (cols J) (primaryIdealGenerator (rows I).val)
  unfold sieveNorm squaredNorm
  rw [he]
  exact hb

end CubicSieve
end

noncomputable section
open scoped BigOperators Classical
namespace CubicSieve

def HasCubicExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M + N^ξ + (M*N)^(2/3 : ℝ))

theorem hasCubicExponent_initial : HasCubicExponent 2 := by
  intro ε hε
  obtain ⟨C,hC,hb⟩ := sieveNorm_initial
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hp : 1 ≤ (M*N)^ε := Real.one_le_rpow
    (one_le_mul_of_one_le_of_one_le hM hN) hε.le
  have hx : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ C*(M+N^2) := hb M N hM hN
    _ ≤ C*(M+N^(2:ℝ)+(M*N)^(2/3:ℝ)) := by
      rw [Real.rpow_two]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hx) hC.le
    _ ≤ _ := by
      rw [mul_assoc C ((M*N)^ε)]
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact le_mul_of_one_le_left (by positivity) hp

lemma HasCubicExponent.swapped {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        sieveNorm M N ≤ C*(M*N)^ε*(M^ξ + N + (M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  rw [sieveNorm_reciprocity]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

lemma HasCubicExponent.doubled {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
        sieveNorm (2*X) N ≤ C*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h.swapped ε hε
  let A : ℝ := 1 + (2:ℝ)^ξ + (2:ℝ)^(2/3 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*(2:ℝ)^ε*A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2/3 : ℝ)
  have hshape : (2*X)^ξ + N + ((2*X)*N)^(2/3 : ℝ) ≤
      A*(X^ξ+N+(X*N)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hxξ]
  calc
    _ ≤ C*((2*X)*N)^ε*((2*X)^ξ+N+((2*X)*N)^(2/3 : ℝ)) := hb (2*X) N (by linarith) hN
    _ ≤ C*((2*X)*N)^ε*(A*(X^ξ+N+(X*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

end CubicSieve
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

theorem primary_extracted_parts (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    primaryIdealGenerator (firstPart I) ≠ 0 ∧ primaryIdealGenerator (secondPart I) ≠ 0 ∧
      primaryIdealGenerator (cubePart I) ≠ 0 := by
  have he := congrArg primaryIdealGeneratorHom
    (cubic_factorization I (primaryIdealGenerator_ne_zero_ideal I hI))
  simp only [map_mul, map_pow] at he
  change primaryIdealGenerator I = primaryIdealGenerator (firstPart I) *
    primaryIdealGenerator (secondPart I) ^ 2 * primaryIdealGenerator (cubePart I) ^ 3 at he
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem firstPart_admissible (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    Admissible (firstPart I) := ⟨firstPart_squarefree I, (primary_extracted_parts I hI).1⟩

theorem secondPart_admissible (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    Admissible (secondPart I) := ⟨secondPart_squarefree I, (primary_extracted_parts I hI).2.1⟩

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
def badPrimeSupport (I : Ideal O) : Finset (Ideal O) :=
  primeSupport I ∩ CanonicalRowCompletion.fixedBadPrimes
def goodPrimeSupport (I : Ideal O) : Finset (Ideal O) :=
  primeSupport I \ CanonicalRowCompletion.fixedBadPrimes
def goodPart (I : Ideal O) : Ideal O := ∏ P ∈ goodPrimeSupport I, P
def badPart (I : Ideal O) : Ideal O := ∏ P ∈ badPrimeSupport I, P

theorem badPrimeSupport_subset (I : Ideal O) :
    badPrimeSupport I ⊆ CanonicalRowCompletion.fixedBadPrimes := Finset.inter_subset_right

theorem goodPart_admissible (I : Ideal O) : Admissible (goodPart I) := by
  have hs : goodPrimeSupport I ⊆ primeSupport I := Finset.sdiff_subset
  refine ⟨squarefree_support_product hs, (goodIdeal_iff_not_ramified _).mpr ?_⟩
  intro hd
  obtain ⟨P,hP,hdiv⟩ := (ramifiedIdeal_prime.dvd_finsetProd_iff (fun P : Ideal O => P)).mp hd
  have hp := support_prime (hs hP)
  have hm : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have he : P = ramifiedIdeal := hm.eq_of_le
    (Ideal.isPrime_of_prime ramifiedIdeal_prime).ne_top (Ideal.dvd_iff_le.mp hdiv)
  exact (Finset.mem_sdiff.mp hP).2 (he ▸ Finset.mem_insert_self _ _)

theorem badPart_mul_goodPart (I : Ideal O) (hI : Squarefree I) :
    badPart I * goodPart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = primeSupport I := by
    ext P
    simp only [badPrimeSupport,goodPrimeSupport,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [badPart,goodPart,←Finset.prod_union hd,hu]
  exact squarefree_support_product_self hI

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  have hd : goodPart I ∣ I := support_product_dvd hI.ne_zero Finset.sdiff_subset
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem fixedBadPrimes_powerset_card :
    CanonicalRowCompletion.fixedBadPrimes.powerset.card = 4 := by
  have hn : ramifiedIdeal ≠ cubicTwoIdeal := by
    intro h
    have he := congrArg Ideal.absNorm h
    rw [ramifiedIdeal_absNorm,cubicTwoIdeal_absNorm] at he
    norm_num at he
  simp [CanonicalRowCompletion.fixedBadPrimes,hn]

end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

def elementCharacter (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) : O →* ℂ where
  toFun x := ringComplex (CubicJacobi.idealSymbol I x)
  map_one' := by rw [←idealRowHom_square,idealRowHom_one_good I hI,one_pow]
  map_mul' x y := by rw [CubicJacobi.idealSymbol_map_mul, map_mul]

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖ringComplex (CubicJacobi.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal O) (B : b → Ideal O) (D : c → O)
    (cols : n → Ideal O) (hc : ∀ j, primaryIdealGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryIdealGenerator (A i) * primaryIdealGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryIdealGenerator (A i) * primaryIdealGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

def extractedGenerator (I : Ideal O) : O :=
  primaryIdealGenerator (goodPart (firstPart I)) *
    primaryIdealGenerator (goodPart (secondPart I)) ^ 2 *
    cubicIdealGenerator (cubePart I) ^ 3 *
    (cubicIdealGenerator (badPart (firstPart I)) * cubicIdealGenerator (badPart (secondPart I)) ^ 2)

theorem span_extractedGenerator (I : Ideal O) (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryIdealGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryIdealGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {cubicIdealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {cubicIdealGenerator (badPart (firstPart I))} *
      Ideal.span {cubicIdealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryIdealGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryIdealGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_cubicIdealGenerator, span_cubicIdealGenerator, span_cubicIdealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction (z : O) (hz : z ≠ 0) :
    ∃ u : Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector (I : Ideal O) :
    ∃ E : CanonicalRowCompletion.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := by
  exact ⟨⟨badPrimeSupport I,
    Finset.mem_powerset.mpr (badPrimeSupport_subset I)⟩, rfl⟩

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalRowCompletion.fixedBadPrimes.powerset ×
      CanonicalRowCompletion.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * cubicIdealGenerator d.2.2.2.val ^ 3 *
    (cubicIdealGenerator (∏ P ∈ d.2.1.val, P) * cubicIdealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryIdealGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := cubic_units_finite
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalRowCompletion.fixedBadPrimes.powerset ×
    CanonicalRowCompletion.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryIdealGenerator p.2.2.val *
    primaryIdealGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryIdealGenerator (goodPart (firstPart I)) *
      primaryIdealGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * cubicIdealGenerator (cubePart I) ^ 3 *
          (cubicIdealGenerator (∏ P ∈ e.val, P) * cubicIdealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D ≤ 96 * (cubeImage R).card := by
    have hu := EisensteinLatticeCount.card_units_le_six
    simp only [D,Fintype.card_prod,Fintype.card_coe,fixedBadPrimes_powerset_card]
    calc
      _ ≤ 6 * (4 * (4 * (cubeImage R).card)) := Nat.mul_le_mul_right _ hu
      _ = _ := by ring
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryIdealGenerator i.val * primaryIdealGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  apply hb.trans
  have hcR : (Fintype.card D : ℝ) ≤ 96 * (cubeImage R).card := by exact_mod_cast hcard
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp only [Fintype.card_coe] at hcR ⊢
  apply mul_le_mul_of_nonneg_right hcR
  exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    EisensteinLatticeCount.finite_ideal_count_real _ X hX
      (fun I hI => primaryIdealGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    EisensteinLatticeCount.finite_ideal_count_real _ Y hY
      (fun I hI => primaryIdealGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply EisensteinLatticeCount.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

def extractionLabel (M : ℝ) (z : O) :
    Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := SchwartzPlanePoisson.CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator
open scoped BigOperators Classical
namespace CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
      _ ≤ _ := cube_scale_power M T ξ hT hTM (by linarith)
  have hn : (M/T)^(1/3 : ℝ)*W*N ≤ M^(1/3 : ℝ)*N := by
    apply mul_le_mul_of_nonneg_right _ hN
    calc
      _ ≤ (M/T)^(1/3 : ℝ)*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_left
        (extracted_linear_le W T (by linarith) hWcube) hH
      _ ≤ _ := cube_scale_power M T (1/3) hT hTM le_rfl
  have hc : (M/T)^(1/3 : ℝ)*W*(U*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
    rw [Real.mul_rpow hU hN, Real.mul_rpow (hT.le.trans hTM) hN]
    calc
      _ = ((M/T)^(1/3 : ℝ)*(W*U^(2/3 : ℝ)))*N^(2/3 : ℝ) := by ring
      _ ≤ ((M/T)^(1/3 : ℝ)*T^(2/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (extracted_monomial_le W U T (2/3) hW hU hWT (by norm_num)) hH)
          (Real.rpow_nonneg hN _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (cube_scale_power M T (2/3) hT hTM (by norm_num))
        (Real.rpow_nonneg hN _)
  nlinarith

theorem extraction_min_shape (M N X Y ξ : ℝ) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : 1 ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < X*Y^2 := by positivity
  have hM0 : 0 < M := hT.trans_le hXY
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hyx : Y ≤ X
  · apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N Y X (X*Y^2) ξ hN hY hX0.le hT hXY
      (by nlinarith) (by nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sq_nonneg Y)]) hξ
  · have hxy : X ≤ Y := (lt_of_not_ge hyx).le
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N X Y (X*Y^2) ξ hN hX hY0.le hT hXY
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hX0.le hY0.le)])
      (by nlinarith [sq_le_sq₀ hX0.le hY0.le |>.mpr hxy]) hξ

lemma cubic_cross_shape_absorb (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    (M*N)^(2/3 : ℝ) ≤ M^(1/3 : ℝ)*N + M^ξ := by
  have hM0 : 0 < M := by linarith
  have hfirst : 0 ≤ M^(1/3 : ℝ)*N := mul_nonneg (Real.rpow_nonneg hM0.le _) hN
  have hsecond : 0 ≤ M^ξ := Real.rpow_nonneg hM0.le _
  by_cases hMN : M ≤ N
  · have hN0 : 0 < N := hM0.trans_le hMN
    have hh := Real.rpow_le_rpow hM0.le hMN (by norm_num : (0 : ℝ) ≤ 1/3)
    have hm : M^(2/3 : ℝ) = M^(1/3 : ℝ)*M^(1/3 : ℝ) := by
      rw [← Real.rpow_add hM0]
      congr 1
      ring
    have hn : N^(1/3 : ℝ)*N^(2/3 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    apply le_trans _ (le_add_of_nonneg_right hsecond)
    rw [Real.mul_rpow hM0.le hN, hm]
    calc
      _ ≤ (M^(1/3 : ℝ)*N^(1/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hM0.le _))
          (Real.rpow_nonneg hN _)
      _ = _ := by rw [mul_assoc, hn]
  · have hNM : N ≤ M := (lt_of_not_ge hMN).le
    apply le_trans _ (le_add_of_nonneg_left hfirst)
    calc
      _ ≤ (M*M)^(2/3 : ℝ) := Real.rpow_le_rpow (mul_nonneg hM0.le hN)
        (mul_le_mul_of_nonneg_left hNM hM0.le) (by norm_num)
      _ = M^(4/3 : ℝ) := by
        rw [Real.mul_rpow hM0.le hM0.le, ← Real.rpow_add hM0]
        congr 1
        ring
      _ ≤ M^ξ := Real.rpow_le_rpow_of_exponent_le hM hξ

theorem extraction_min_two_power (M N X Y ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : (4/3 : ℝ) ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      2*(M^(1/3 : ℝ)*N + M^ξ) := by
  have hh := extraction_min_shape M N X Y ξ hN hX hY hXY (by linarith)
  have hc := cubic_cross_shape_absorb M N ξ hM hN hξ
  linarith

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace InverseMoment
theorem ideal_coprime_mobius (K P : Ideal Eisenstein.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]


end InverseMoment
namespace CubicSieve
theorem gcd_eq_iff_quotient_coprime (D I J : Ideal O) (hD : D ≠ 0)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (quadraticIdealQuotient D I) (quadraticIdealQuotient D J) := by
  have he : gcd I J = D * gcd (quadraticIdealQuotient D I) (quadraticIdealQuotient D J) := by
    calc
      gcd I J = gcd (D * quadraticIdealQuotient D I) (D * quadraticIdealQuotient D J) := by
        rw [quadraticIdeal_mul_quotient hDI, quadraticIdeal_mul_quotient hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

def totalQuotient (D I : Ideal O) : Ideal O :=
  if D ∣ I then quadraticIdealQuotient D I else 1

def gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => gcd (cols p.1) (cols p.2))

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem gcdPool_ne_zero {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀ j, cols j ≠ 0) (D : Ideal O) (hD : D ∈ gcdPool cols) : D ≠ 0 := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  intro h
  have hd := gcd_dvd_left (cols j) (cols k)
  rw [h, zero_dvd_iff] at hd
  exact hcols j hd


end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  

noncomputable section
local notation "O" => Eisenstein.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  ringComplex (CubicJacobi.idealSymbol I z)

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryIdealGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius (D : Ideal O) (hD : primaryIdealGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact InverseMoment.ideal_coprime_mobius D _ (primaryIdealGenerator_ne_zero_ideal D hD)

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryIdealGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

lemma cubic_admissible_quotient {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (quadraticIdealQuotient D I) :=
  cubic_admissible_of_dvd hI (quadraticIdealQuotient_dvd hD)

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (quadraticIdealQuotient D I) z := by
  conv_lhs => rw [← quadraticIdeal_mul_quotient hDI]
  exact cubicRow_mul _ _ _

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, if_pos hj, if_pos hk]
      rw [← gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [if_pos hg, if_pos hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [if_neg hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [cubicGcdTerm, if_neg hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [cubicGcdTerm, if_neg hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [cubicGcdTerm, ite_true]
    · intro D hD hne
      exact if_neg (Ne.symm hne)
    · exact fun h => (h (mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  rw [←Finset.sum_mul_sum, ←star_sum]
  simpa only [Complex.star_def, Complex.ofReal_pow] using
    (Complex.conj_mul' (∑ j, cubicRow (cols j) z * a j)).symm

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

/-- Nonzero Eisenstein rows of bounded absolute norm. -/
def elementRange (M : ℝ) : Finset O :=
  (Eisenstein.finite_norm_sublevel (Real.sqrt (max 0 M))).toFinset.filter
    (fun z => z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)

lemma mem_elementRange (M : ℝ) (z : O) :
    z ∈ elementRange M ↔ z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    rw [Set.Finite.mem_toFinset]
    apply (Real.le_sqrt (norm_nonneg _) (le_max_left 0 M)).mpr
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact h.2.trans (le_max_right 0 M)

def elementMatrix (M N : ℝ) : Matrix (elementRange M) (idealRange N) ℂ :=
  fun z J => cubicRow J.val z.val

def elementSieveNorm (M N : ℝ) : ℝ := squaredNorm (elementMatrix M N)

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg (fun I : elementRange M => I.val) h)
  have hci : Function.Injective c := fun i j h => hc (congrArg (fun I : idealRange N => I.val) h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryIdealGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    change primaryIdealGenerator I.val = primaryIdealGenerator J.val at he
    apply Subtype.ext
    rw [←(primaryIdealGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1,
      ←(primaryIdealGenerator_spec J.val (mem_idealRange.mp J.property).1.2).1, he]
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryIdealGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

lemma elementSieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    elementSieveNorm M N ≤ elementSieveNorm M' N' := by
  apply element_family_squared_norm_le (fun z : elementRange M => z.val)
    (fun I : idealRange N => I.val) Subtype.val_injective Subtype.val_injective
  · intro z
    exact ⟨((mem_elementRange M z.val).mp z.property).1,
      ((mem_elementRange M z.val).mp z.property).2.trans hM⟩
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hN⟩

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ DivisorBlockCauchy.divisorConstant ε hε * N ^ ε :=
    mul_nonneg (DivisorBlockCauchy.divisorConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  simp only [←Ideal.isCoprime_iff_sup_eq] at hb
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

/-- The initial cubic estimate applies to every nonzero lattice row. -/
theorem elementSieveNorm_initial : ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    elementSieveNorm M N ≤ C * (M + N ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := primeSubsetRow_initial_operator_bound
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  let cols : idealRange N → CubicIdeal := fun I => ⟨I.val, (mem_idealRange.mp I.property).1⟩
  have hc : Function.Injective cols := fun I J h => Subtype.ext (congrArg (fun I : CubicIdeal => I.val) h)
  have hb := hbound primeGenerator primeGenerator_ne_zero primeGenerator_span_injective
    (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
    (fun P => complexCubicChar_ne_one _ (primeGenerator_good P))
    (fun z : elementRange M => z.val) Subtype.val_injective
    (fun J => idealSupport (cols J)) (idealSupport_injective.comp hc) M N hM hN
    (fun z => by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact ((mem_elementRange M z.val).mp z.property).2)
    (fun J => by rw [idealSupport_norm]; exact (mem_idealRange.mp J.property).2)
  have he : elementMatrix M N = fun z J => primeSubsetRow primeGenerator
      (fun P => complexCubicChar (Ideal.span {primeGenerator P}) (primeGenerator_good P))
      (idealSupport (cols J)) z.val := by
    ext z J
    exact idealSymbol_eq_primeSubsetRow (cols J) z.val
  unfold elementSieveNorm squaredNorm
  rw [he]
  exact hb

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  

noncomputable section
local notation "O" => Eisenstein.O

def elementQuotient (d z : O) : O := if h : d ∣ z then h.choose else 0

lemma elementQuotient_mul (d z : O) (h : d ∣ z) : d * elementQuotient d z = z := by
  rw [elementQuotient, dif_pos h]
  exact h.choose_spec.symm

lemma elementQuotient_injective (d : O) : Set.InjOn (elementQuotient d) {z | d ∣ z} := by
  intro x hx y hy he
  rw [← elementQuotient_mul d x hx, ← elementQuotient_mul d y hy, he]

def dividedRows (R : Finset O) (d : O) : Finset O :=
  (R.filter (fun z => d ∣ z)).image (elementQuotient d)

lemma sum_divisible_rows (R : Finset O) (d : O) (f : O → ℂ) :
    (∑ z ∈ R, if d ∣ z then f z else 0) =
      ∑ w ∈ dividedRows R d, f (d * w) := by
  rw [← Finset.sum_filter]
  unfold dividedRows
  have hinj : Set.InjOn (elementQuotient d) (↑(R.filter (fun z => d ∣ z)) : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective d (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro z hz
  rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]

lemma dividedRows_ne_zero (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0) (d : O)
    (w : O) (hw : w ∈ dividedRows R d) : w ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  intro he
  have h := elementQuotient_mul d z (Finset.mem_filter.mp hz).2
  rw [he, mul_zero] at h
  exact hR z (Finset.mem_filter.mp hz).1 h.symm

lemma dividedRows_norm_le (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (d : O) (hd : d ≠ 0) (w : O) (hw : w ∈ dividedRows R d) :
    (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ M / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  have hdN : 0 < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hd))
  apply (le_div_iff₀ hdN).mpr
  calc
    _ = (Ideal.absNorm (Ideal.span {d * elementQuotient d z}) : ℝ) := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm (Ideal.span {z}) : ℝ) := by
      rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]
    _ ≤ M := hR z (Finset.mem_filter.mp hz).1

lemma cubicRow_mul_argument (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (x y : O) :
    cubicRow I (x * y) = cubicRow I x * cubicRow I y := by
  exact (elementCharacter I hI).map_mul x y

lemma totalQuotient_cubic_admissible (D I : Ideal O) (hI : Admissible I) :
    Admissible (totalQuotient D I) := by
  by_cases h : D ∣ I
  · rw [totalQuotient, if_pos h]
    exact cubic_admissible_quotient hI h
  · rw [totalQuotient, if_neg h]
    exact ⟨squarefree_one, by rw [primaryIdealGenerator_one]; exact one_ne_zero⟩

def descendedCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) : ℂ :=
  cubicRow (totalQuotient D (cols j)) d * (if D ∣ cols j then a j else 0)

def residualGram {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
    star (cubicRow (totalQuotient D (cols j)) z * a j) *
      (cubicRow (totalQuotient D (cols k)) z * a k) else 0

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols j)).2,
      cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols k)).2]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl

lemma ideal_dvd_span_iff_generator (E : Ideal O) (z : O) :
    E ∣ Ideal.span {z} ↔ cubicIdealGenerator E ∣ z := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have he : (z ∈ Ideal.span {cubicIdealGenerator E}) ↔ cubicIdealGenerator E ∣ z :=
    Ideal.mem_span_singleton
  rwa [span_cubicIdealGenerator] at he

lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols hcols a]

theorem cubic_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryIdealGenerator D ≠ 0)
    (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (cubicIdealGenerator E),
            w (cubicIdealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (cubicIdealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      (star (cubicRow D z) * cubicRow D z) * residualGram D cols b z := by
    simp only [cubicGcdTerm_eq_quotient D (primaryIdealGenerator_ne_zero_ideal D hD),
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if cubicIdealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, cubicRow_common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if cubicIdealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols hcols a R w (cubicIdealGenerator E))

end
end CubicSieve

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
