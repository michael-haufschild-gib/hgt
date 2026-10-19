import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeQuartic
import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression

/-!
# Actual finite arithmetic edge families

Ramanujan inversion realizes every real profile on twice-products of finite
coprime odd blocks. The cutoff admits every order, including empty support.
Affine data give exactly the edge magnitudes; fourth arrays give exactly
the triangle and cycle equations, even against arbitrary sieve competitors.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges.Blocks
open GaloisForLFunctions.BezoutValuationIncidence
open AffineSieve
set_option autoImplicit false
variable {V : Type*} [Fintype V] (D : Blocks V)

/-- A cutoff admitting every block and every edge order, including the empty family. -/
def cutoff (n : ℕ) : ℕ := 2 + (∑ u, ∑ v, D.order u v) + n

theorem cutoff_two_le (n : ℕ) : 2 ≤ D.cutoff n := by unfold cutoff; omega

omit [Fintype V] in
theorem order_pos (u v : V) : 0 < D.order u v := by
  have hu := D.gt_one u
  have hv := D.gt_one v
  unfold order
  positivity

theorem order_mem_cutoff (n : ℕ) (u v : V) :
    D.order u v ∈ Finset.Icc 1 (D.cutoff n) := by
  have hv : D.order u v ≤ ∑ w, D.order u w :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hu : (∑ w, D.order u w) ≤ ∑ z, ∑ w, D.order z w :=
    Finset.single_le_sum (f := fun z => ∑ w, D.order z w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  refine Finset.mem_Icc.mpr ⟨D.order_pos u v,?_⟩
  unfold cutoff
  omega

theorem value_mem_cutoff (n : ℕ) (u : V) : D.value u ∈ Finset.Icc 1 (D.cutoff n) := by
  have hp := D.gt_one u
  have hb : 1 ≤ D.value u := by omega
  have hm := Nat.mul_le_mul_left (D.value u) hb
  simp only [mul_one] at hm
  have ho := (Finset.mem_Icc.mp (D.order_mem_cutoff n u u)).2
  unfold order at ho
  exact Finset.mem_Icc.mpr ⟨hb,by nlinarith⟩

/-- Real coordinates prescribed only at nonloop arithmetic edge orders. -/
def profile (a : ℕ → ℝ) (q : ℕ) : ℝ := by
  classical
  exact if ∃ u v, u ≠ v ∧ q = D.order u v then a q else 0

theorem profile_order (a : ℕ → ℝ) {u v : V} (huv : u ≠ v) :
    D.profile a (D.order u v) = a (D.order u v) := by
  exact if_pos ⟨u,v,huv,rfl⟩

theorem profile_zero (a : ℕ → ℝ) (q : ℕ)
    (hq : ¬ ∃ u v, u ≠ v ∧ q = D.order u v) : D.profile a q = 0 := if_neg hq

/-- Canonical divisor weights realizing the entire finite edge profile. -/
def weights (n : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (D.profile a) (D.cutoff n)

theorem coordinate_weights (n : ℕ) (a : ℕ → ℝ) (q : ℕ) :
    selbergMultiplesCoord (D.cutoff n) (D.weights n a) q = D.profile a q := by
  rw [weights,selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Finset.Icc 1 (D.cutoff n)
  · rw [if_pos hq]
  · rw [if_neg hq]
    symm
    apply D.profile_zero
    rintro ⟨u,v,_,rfl⟩
    exact hq (D.order_mem_cutoff n u v)

theorem weights_supported (n : ℕ) (a : ℕ → ℝ) : D.EdgeSupported (D.cutoff n) (D.weights n a) := by
  intro q hq
  rw [D.coordinate_weights,D.profile_zero a q hq]

/-- The prescribed symmetric edge array, with zero diagonal. -/
def edgeAmplitude (a : ℕ → ℝ) (u v : V) : ℝ := by
  classical
  exact if u = v then 0 else a (D.order u v)

theorem edgeCoord_weights (n : ℕ) (a : ℕ → ℝ) :
    D.edgeCoord (D.cutoff n) (D.weights n a) = D.edgeAmplitude a := by
  classical
  funext u v
  by_cases huv : u = v
  · simp only [edgeCoord,edgeAmplitude,if_pos huv]
  · simp only [edgeCoord,edgeAmplitude,if_neg huv,D.coordinate_weights,D.profile_order a huv]

/-- Every supported cutoff signal has a canonical realization in this actual family. -/
theorem signal_realization (n : ℕ) (c : ℕ → ℝ) (hc : D.EdgeSupported (D.cutoff n) c) (k : ℕ) :
    sieveSeq (D.cutoff n) c k =
      sieveSeq (D.cutoff n) (D.weights n (selbergMultiplesCoord (D.cutoff n) c)) k := by
  classical
  have he : ∀ d ∈ Finset.Icc 1 (D.cutoff n),
      c d = D.weights n (selbergMultiplesCoord (D.cutoff n) c) d := by
    apply (sieve_active_coefficients_eq_iff _ _ _).mpr
    intro q _
    rw [D.coordinate_weights]
    by_cases hq : ∃ u v, u ≠ v ∧ q = D.order u v
    · simp only [profile,if_pos hq]
    · rw [D.profile_zero _ q hq,hc q hq]
  unfold sieveSeq
  apply Finset.sum_congr rfl
  intro d hd
  exact he d (Finset.mem_filter.mp hd).1

/-- The complete quartic fibre of each explicitly realized finite edge signal. -/
theorem fourth_weights_iff (n : ℕ) (a e : ℕ → ℝ) :
    (∀ h : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) e h) ↔
      D.EdgeSupported (D.cutoff n) e ∧
        QuarticRelations (D.edgeAmplitude a) (D.edgeCoord (D.cutoff n) e) := by
  simpa only [D.edgeCoord_weights] using
    D.fourth_moments_iff (D.cutoff n) (D.cutoff_two_le n) (D.value_mem_cutoff n)
      (D.weights n a) e (D.weights_supported n a)

theorem fourth_between_weights_iff (n : ℕ) (a b : ℕ → ℝ) :
    (∀ h : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h) ↔
      QuarticRelations (D.edgeAmplitude a) (D.edgeAmplitude b) := by
  rw [D.fourth_weights_iff,D.edgeCoord_weights]
  exact and_iff_right (D.weights_supported n b)

private theorem profile_product_of_squares (a b : ℕ → ℝ)
    (hsq : ∀ u v, u ≠ v → a (D.order u v)^2 = b (D.order u v)^2)
    (q d : ℕ) (hdq : d ∣ q) :
    D.profile a q * D.profile a d = D.profile b q * D.profile b d := by
  classical
  by_cases hq : ∃ u v, u ≠ v ∧ q = D.order u v
  · obtain ⟨u,v,huv,rfl⟩ := hq
    by_cases hd : ∃ x y, x ≠ y ∧ d = D.order x y
    · obtain ⟨x,y,hxy,rfl⟩ := hd
      rcases (D.order_dvd_iff hxy).mp hdq with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · subst x; subst y
        simpa only [D.profile_order a huv,D.profile_order b huv,pow_two] using hsq u v huv
      · subst x; subst y
        rw [D.order_symm v u]
        simpa only [D.profile_order a huv,D.profile_order b huv,pow_two] using hsq u v huv
    · rw [D.profile_zero a d hd,D.profile_zero b d hd,mul_zero,mul_zero]
  · rw [D.profile_zero a q hq,D.profile_zero b q hq,zero_mul,zero_mul]

/-- Affine data give precisely the magnitudes on the incomparable edge orders. -/
theorem affine_weights_iff_squares (n : ℕ) (a b : ℕ → ℝ) :
    (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
      affineMoment (D.cutoff n) (D.weights n b) s t) ↔
      ∀ u v, u ≠ v → a (D.order u v)^2 = b (D.order u v)^2 := by
  rw [affineMoment_eq_iff_comparable]
  constructor
  · intro h u v huv
    have he := h (D.order u v) (D.order_mem_cutoff n u v) (D.order u v)
      (Nat.mem_divisors.mpr ⟨dvd_refl _,Nat.ne_of_gt (D.order_pos u v)⟩)
    simpa only [D.coordinate_weights,D.profile_order a huv,D.profile_order b huv,pow_two] using he
  · intro h q _ d hd
    simp only [D.coordinate_weights]
    exact D.profile_product_of_squares a b h q d (Nat.dvd_of_mem_divisors hd)

theorem coordinate_squares (n : ℕ) (a b : ℕ → ℝ)
    (hsq : ∀ u v, u ≠ v → a (D.order u v)^2 = b (D.order u v)^2) (q : ℕ) :
    selbergMultiplesCoord (D.cutoff n) (D.weights n a) q ^ 2 =
      selbergMultiplesCoord (D.cutoff n) (D.weights n b) q ^ 2 := by
  simpa only [D.coordinate_weights,pow_two] using
    D.profile_product_of_squares a b hsq q q (dvd_refl q)

/-- Affine observations also force arbitrary competing signals into the realized family. -/
theorem affine_partner_realization (n : ℕ) (a e : ℕ → ℝ)
    (haff : ∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
      affineMoment (D.cutoff n) e s t) :
    ∃ b : ℕ → ℝ, ∀ k, sieveSeq (D.cutoff n) e k =
      sieveSeq (D.cutoff n) (D.weights n b) k := by
  classical
  let b : ℕ → ℝ := selbergMultiplesCoord (D.cutoff n) e
  refine ⟨b,?_⟩
  have hc := (affineMoment_eq_iff_comparable (D.cutoff n) (D.weights n a) e).mp haff
  have he : ∀ d ∈ Finset.Icc 1 (D.cutoff n), e d = D.weights n b d := by
    apply (sieve_active_coefficients_eq_iff _ _ _).mpr
    intro q hq
    by_cases hm : ∃ u v, u ≠ v ∧ q = D.order u v
    · rw [D.coordinate_weights]
      simp only [profile,if_pos hm,b]
    · have hh := hc q hq q (Nat.mem_divisors.mpr
        ⟨dvd_refl q,by have := (Finset.mem_Icc.mp hq).1; omega⟩)
      rw [D.coordinate_weights,D.profile_zero a q hm,zero_mul] at hh
      have hz : selbergMultiplesCoord (D.cutoff n) e q = 0 := mul_self_eq_zero.mp hh.symm
      rw [hz,D.coordinate_weights,D.profile_zero b q hm]
  intro k
  unfold sieveSeq
  apply Finset.sum_congr rfl
  intro d hd
  exact he d (Finset.mem_filter.mp hd).1

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges.Blocks
