import GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation
/-!
# Subpower remainder of the actual coprime residue head

Complete Möbius columns isolate the quadratic harmonic coefficient at every
initial coordinate. The remaining weighted signed head has arbitrarily small
power growth, unconditionally. The retained quadratic coefficient and the
complete later tail still require their joint estimate; no RH ceiling follows
from the head remainder alone.
-/
noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHTower.DeletionCoprimeHead
open Sieve DeletionCoprimeColumn

private def pairForm (N : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N,
    (if d.Coprime e then ((μ d : ℤ) : ℝ)*((μ e : ℤ) : ℝ) else 0)*f d*g e

private theorem pairForm_symm (N : ℕ) (f g : ℕ → ℝ) :
    pairForm N f g = pairForm N g f := by
  unfold pairForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : d.Coprime e
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun he => h he.symm)]; ring

private theorem pairForm_sub_square (N : ℕ) (f g : ℕ → ℝ) :
    pairForm N (fun d => f d-g d) (fun d => f d-g d) =
      pairForm N f f-2*pairForm N f g+pairForm N g g := by
  have h := pairForm_symm N f g
  have he : pairForm N (fun d => f d-g d) (fun d => f d-g d) =
      pairForm N f f-pairForm N f g-pairForm N g f+pairForm N g g := by
    simp only [pairForm, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, ← h]
  ring

private theorem pairForm_left_scale (N : ℕ) (f g : ℕ → ℝ) (c : ℝ) :
    pairForm N (fun d => c*f d) g = c*pairForm N f g := by
  unfold pairForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Coefficient of the exact quadratic part of a coprime residue head. -/
def harmonicQuadratic (N : ℕ) : ℝ := pairForm N (fun d => 1/d) (fun d => 1/d)

/-- Actual coprime residue quadratic at one integer coordinate. -/
def residueQuadratic (N t : ℕ) : ℝ :=
  pairForm N (fun d => ((t%d : ℕ) : ℝ)/d) (fun d => ((t%d : ℕ) : ℝ)/d)

/-- Signed reciprocal outer column after complete coprime inversion. -/
def mixedColumn (N t : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ)/(d : ℝ)*((primeSupportedIcc d t).card : ℝ)

private theorem truncated_column {N t : ℕ} (htN : t≤N) (d : ℕ) :
    (∑ e ∈ Icc 1 N, (if d.Coprime e then ((μ e : ℤ) : ℝ) else 0)*(t/e : ℕ)) =
      ((primeSupportedIcc d t).card : ℝ) := by
  rw [← complete_floor_column d t]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl htN)
  intro e he hnot
  have ht : t<e := by
    have he1 := (mem_Icc.mp he).1
    by_contra h
    exact hnot (mem_Icc.mpr ⟨he1, by omega⟩)
  simp [Nat.div_eq_of_lt ht]

private theorem pairForm_floor_column {N t : ℕ} (htN : t≤N) (f : ℕ → ℝ) :
    pairForm N f (fun e => (t/e : ℕ)) =
      ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℝ)*f d*((primeSupportedIcc d t).card : ℝ) := by
  unfold pairForm
  apply Finset.sum_congr rfl
  intro d _
  rw [← truncated_column htN d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : d.Coprime e
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- Complete-column cancellation isolates the exact quadratic head term at every initial coordinate. -/
theorem residueQuadratic_eq {N t : ℕ} (htN : t≤N) :
    residueQuadratic N t = (t : ℝ)^2*harmonicQuadratic N-
      2*t*mixedColumn N t+floorCorrelation (Icc 1 N) t := by
  have hmod : ∀ d ∈ Icc 1 N, ((t%d : ℕ) : ℝ)/d =
      (t : ℝ)*(1/d)-(t/d : ℕ) := by
    intro d hd
    have hd0 : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hd).1)
    have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div t d)
    push_cast at he
    field_simp
    nlinarith
  have hfun : residueQuadratic N t = pairForm N
      (fun d => (t : ℝ)*(1/d)-(t/d : ℕ))
      (fun d => (t : ℝ)*(1/d)-(t/d : ℕ)) := by
    unfold residueQuadratic pairForm
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    dsimp only
    rw [hmod d hd, hmod e he]
  rw [hfun, pairForm_sub_square, pairForm_left_scale,
    pairForm_symm N (fun d => 1/d) (fun d => (t : ℝ)*(1/d)), pairForm_left_scale]
  have hmix : pairForm N (fun d => (t : ℝ)*(1/d)) (fun e => (t/e : ℕ)) =
      (t : ℝ)*mixedColumn N t := by
    rw [pairForm_left_scale, pairForm_floor_column htN]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hfloor : pairForm N (fun d => (t/d : ℕ)) (fun e => (t/e : ℕ)) =
      floorCorrelation (Icc 1 N) t := by
    rw [pairForm_floor_column htN]
    have hs : Icc 1 N ∩ Icc 1 t = Icc 1 t :=
      inter_eq_right.mpr (Icc_subset_Icc le_rfl htN)
    simp only [floorCorrelation, hs, complete_floor_column]
    symm
    apply Finset.sum_subset (Icc_subset_Icc le_rfl htN)
    intro d hd hnot
    have htd : t<d := by
      have hd1 := (mem_Icc.mp hd).1
      by_contra h
      exact hnot (mem_Icc.mpr ⟨hd1, by omega⟩)
    simp [Nat.div_eq_of_lt htd]
  rw [hmix, hfloor]
  change _ = _*pairForm N (fun d => 1/d) (fun d => 1/d)-_+_
  ring

private theorem exists_mixedColumn_bound {δ : ℝ} (hδ : 0<δ) :
    ∃ C : ℝ, 0<C ∧ ∀ N t : ℕ, 0<t → t≤N →
      |mixedColumn N t| ≤ C*(N : ℝ)^(2*δ)*(1+Real.log N) := by
  obtain ⟨C,hC,hcount⟩ := exists_supportedCount_le hδ hδ
  refine ⟨C,hC,?_⟩
  intro N t ht htN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast lt_of_lt_of_le ht htN
  have htp : (t : ℝ)^δ ≤ (N : ℝ)^δ :=
    Real.rpow_le_rpow (Nat.cast_nonneg t) (by exact_mod_cast htN) hδ.le
  have hterm (d : ℕ) (hd : d∈Icc 1 N) :
      |((μ d : ℤ) : ℝ)/(d : ℝ)*((primeSupportedIcc d t).card : ℝ)| ≤
        (C*(N : ℝ)^(2*δ))*(1/(d : ℝ)) := by
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdp : (d : ℝ)^δ ≤ (N : ℝ)^δ :=
      Real.rpow_le_rpow hd0.le (by exact_mod_cast (mem_Icc.mp hd).2) hδ.le
    have hs : ((primeSupportedIcc d t).card : ℝ) ≤ C*(N : ℝ)^(2*δ) := by
      calc
        _ ≤ C*(t : ℝ)^δ*(d : ℝ)^δ := hcount d t (mem_Icc.mp hd).1 ht
        _ ≤ C*(N : ℝ)^δ*(N : ℝ)^δ :=
          mul_le_mul (mul_le_mul_of_nonneg_left htp hC.le) hdp (by positivity) (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; congr 2; ring
    have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    calc
      _ = (|((μ d : ℤ) : ℝ)|/(d : ℝ))*((primeSupportedIcc d t).card : ℝ) := by
        rw [abs_mul, abs_div, abs_of_pos hd0,
          abs_of_nonneg (show (0 : ℝ)≤((primeSupportedIcc d t).card : ℝ) by positivity)]
      _ ≤ (1/(d : ℝ))*(C*(N : ℝ)^(2*δ)) :=
        mul_le_mul (div_le_div_of_nonneg_right hmu hd0.le) hs (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |((μ d : ℤ) : ℝ)/(d : ℝ)*((primeSupportedIcc d t).card : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, (C*(N : ℝ)^(2*δ))*(1/(d : ℝ)) := Finset.sum_le_sum hterm
    _ = (C*(N : ℝ)^(2*δ))*(∑ d ∈ Icc 1 N, 1/(d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) (by positivity)

/-- The signed coprime residue quadratic summed through its coefficient cutoff. -/
def initialEnergy (N : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 N, residueQuadratic N t/((t : ℝ)*(t+1))

/-- Exact weight of the quadratic head term. -/
def headMass (N : ℕ) : ℝ := ∑ t ∈ Icc 1 N, (t : ℝ)/(t+1)

/-- After its exact arithmetic quadratic term is removed, the initial-range remainder
has arbitrarily small power growth, without an RH or cancellation hypothesis. -/
theorem exists_initialEnergy_remainder_subpower {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ,
      |initialEnergy N-harmonicQuadratic N*headMass N| ≤ C*(N : ℝ)^ε := by
  let δ : ℝ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨A,hA,hL⟩ := exists_mixedColumn_bound hδ
  obtain ⟨B,hB,hF⟩ := exists_floorCorrelation_le hδ
  let D : ℝ := 1+1/δ
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨2*A*D^2+B*D, by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [initialEnergy, headMass, Real.zero_rpow hε.ne']
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  let H : ℝ := 1+Real.log N
  have hH : 0≤H := by dsimp [H]; linarith [Real.log_nonneg hN1]
  let K : ℝ := 2*A*(N : ℝ)^(2*δ)*H+B*(N : ℝ)^δ
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (t : ℕ) (ht : t∈Icc 1 N) :
      |(residueQuadratic N t-(t : ℝ)^2*harmonicQuadratic N)/((t : ℝ)*(t+1))| ≤
        K*(1/(t : ℝ)) := by
    have ht0 : (0 : ℝ)<t := by exact_mod_cast (mem_Icc.mp ht).1
    have htp : (t : ℝ)^δ ≤ (N : ℝ)^δ :=
      Real.rpow_le_rpow ht0.le (by exact_mod_cast (mem_Icc.mp ht).2) hδ.le
    have hfloor : |floorCorrelation (Icc 1 N) t| ≤ B*(N : ℝ)^δ*t := by
      calc
        _ ≤ B*(t : ℝ)^(1+δ) := hF (Icc 1 N) t
        _ = B*(t : ℝ)^δ*t := by rw [Real.rpow_add ht0, Real.rpow_one]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htp hB.le) ht0.le
    have hnum : |residueQuadratic N t-(t : ℝ)^2*harmonicQuadratic N| ≤ K*t := by
      rw [residueQuadratic_eq (mem_Icc.mp ht).2]
      have he : (t : ℝ)^2*harmonicQuadratic N-2*t*mixedColumn N t+
          floorCorrelation (Icc 1 N) t-(t : ℝ)^2*harmonicQuadratic N =
          -(2*(t : ℝ)*mixedColumn N t)+floorCorrelation (Icc 1 N) t := by ring
      rw [he]
      calc
        _ ≤ |-(2*(t : ℝ)*mixedColumn N t)|+|floorCorrelation (Icc 1 N) t| := abs_add_le _ _
        _ = 2*(t : ℝ)*|mixedColumn N t|+|floorCorrelation (Icc 1 N) t| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ)≤2*t)]
        _ ≤ 2*(t : ℝ)*(A*(N : ℝ)^(2*δ)*H)+B*(N : ℝ)^δ*t :=
          add_le_add (mul_le_mul_of_nonneg_left
            (hL N t (mem_Icc.mp ht).1 (mem_Icc.mp ht).2) (by positivity)) hfloor
        _ = _ := by dsimp [K]; ring
    calc
      _ = |residueQuadratic N t-(t : ℝ)^2*harmonicQuadratic N|/((t : ℝ)*(t+1)) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ)<(t : ℝ)*(t+1))]
      _ ≤ (K*t)/((t : ℝ)*(t+1)) := div_le_div_of_nonneg_right hnum (by positivity)
      _ = K/(t+1) := by field_simp
      _ ≤ K/(t : ℝ) := div_le_div_of_nonneg_left hK ht0 (by linarith)
      _ = _ := by ring
  have hsum : initialEnergy N-harmonicQuadratic N*headMass N =
      ∑ t ∈ Icc 1 N, (residueQuadratic N t-(t : ℝ)^2*harmonicQuadratic N)/((t : ℝ)*(t+1)) := by
    rw [initialEnergy, headMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht0 : (t : ℝ)≠0 := by exact_mod_cast (show t≠0 by have := (mem_Icc.mp ht).1; omega)
    field_simp
  have hb : |initialEnergy N-harmonicQuadratic N*headMass N| ≤ K*H := by
    rw [hsum]
    calc
      _ ≤ ∑ t ∈ Icc 1 N, |(residueQuadratic N t-(t : ℝ)^2*harmonicQuadratic N)/((t : ℝ)*(t+1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Icc 1 N, K*(1/(t : ℝ)) := Finset.sum_le_sum hpoint
      _ = K*(∑ t ∈ Icc 1 N, 1/(t : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log N) hK
  have hlog : H ≤ D*(N : ℝ)^δ := by
    have hp := Real.one_le_rpow hN1 hδ.le
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg N) hδ
    dsimp [H, D]
    calc
      _ ≤ (N : ℝ)^δ+(N : ℝ)^δ/δ := add_le_add hp hl
      _ = _ := by ring
  have hpowers : (N : ℝ)^(2*δ)*(N : ℝ)^δ*(N : ℝ)^δ = (N : ℝ)^ε := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    dsimp [δ]
    ring
  have hsmall : (N : ℝ)^δ*(N : ℝ)^δ ≤ (N : ℝ)^ε := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [δ]; linarith)
  calc
    _ ≤ K*H := hb
    _ = 2*A*(N : ℝ)^(2*δ)*(H*H)+B*(N : ℝ)^δ*H := by dsimp [K]; ring
    _ ≤ 2*A*(N : ℝ)^(2*δ)*((D*(N : ℝ)^δ)*(D*(N : ℝ)^δ))+
        B*(N : ℝ)^δ*(D*(N : ℝ)^δ) :=
      add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul hlog hlog hH (by positivity)) (by positivity))
        (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ = 2*A*D^2*(N : ℝ)^ε+B*D*((N : ℝ)^δ*(N : ℝ)^δ) := by
      calc
        _ = 2*A*D^2*((N : ℝ)^(2*δ)*(N : ℝ)^δ*(N : ℝ)^δ)+B*D*((N : ℝ)^δ*(N : ℝ)^δ) := by ring
        _ = _ := by rw [hpowers]
    _ ≤ 2*A*D^2*(N : ℝ)^ε+B*D*(N : ℝ)^ε :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ)≤B*D by positivity))
    _ = _ := by ring

end RHTower.DeletionCoprimeHead
