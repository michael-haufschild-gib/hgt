import GaloisForLFunctions.RHTower.BandKaiserPacketConditioning
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Uniform energy lower bounds for conditioned Kaiser packet spans

The packet-reading matrix has a positive diagonal of size at least `T_c(0)/2` and exponentially
small off-diagonal entries.  A maximal-coefficient argument therefore gives a quantitative lower
bound for every vector in a fixed finite packet span.  Integral Cauchy--Schwarz then converts one
large reading into physical `L²` energy.
-/

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Conditioned Kaiser combination on the explicit angular grid. -/
def kaiserGridCombination {m : ℕ} (c : ℝ) (b : Fin m → ℝ) : ℝ → ℝ :=
  kaiserCosCombination c (kaiserPacketFrequency c) b

/-- A row of the packet-reading matrix applied to the coefficient vector. -/
def kaiserPacketRow {m : ℕ} (c : ℝ) (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
    (kaiserPacketAngularFrequency c j)

theorem exists_max_abs_kaiserPacketCoefficient {m : ℕ} (hm : 0 < m) (b : Fin m → ℝ) :
    ∃ i : Fin m, ∀ j : Fin m, |b j| ≤ |b i| := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m))
    (fun j => |b j|) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem sum_sq_kaiserPacketCoefficient_le {m : ℕ} (b : Fin m → ℝ) (i : Fin m)
    (hi : ∀ j, |b j| ≤ |b i|) :
    (∑ j, b j ^ (2 : ℕ)) ≤ (m : ℝ) * |b i| ^ (2 : ℕ) := by
  calc
    (∑ j, b j ^ (2 : ℕ)) = ∑ j, |b j| ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (sq_abs (b j)).symm
    _ ≤ ∑ _j : Fin m, |b i| ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2
    _ = (m : ℝ) * |b i| ^ (2 : ℕ) := by simp [Fintype.card_fin]

/-- Diagonal dominance of a fixed packet row at an index of maximal coefficient magnitude. -/
theorem abs_kaiserPacketRow_ge {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c)
    (hsmall : 32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2)) ≤ 1)
    (b : Fin m → ℝ) (i : Fin m) (hi : ∀ j, |b j| ≤ |b i|) :
    |b i| * kaiserAngularTransform c 0 / 4 ≤ |kaiserPacketRow c b i| := by
  let T : ℝ := kaiserAngularTransform c 0
  let D : ℝ := kaiserPacketReading c (kaiserPacketAngularFrequency c i)
    (kaiserPacketAngularFrequency c i)
  let E : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
    b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
      (kaiserPacketAngularFrequency c j)
  have hcpos : 0 < c := one_pos.trans_le hc
  have hTpos : 0 < T := by
    exact kaiserAngularTransform_zero_pos hcpos
  have hD : T / 2 ≤ D := by
    exact kaiserPacketReading_diagonal_ge hc hscale i
  have hD0 : 0 ≤ D := le_trans (div_nonneg hTpos.le (by norm_num)) hD
  have hdiag : |b i| * T / 2 ≤ |b i * D| := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact div_le_iff₀ (by norm_num : (0 : ℝ) < 2) |>.2
      (by nlinarith [mul_le_mul_of_nonneg_left hD (abs_nonneg (b i))])
  have hoff : |E| ≤
      (m : ℝ) * (|b i| *
        (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
    calc
      |E| ≤ ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
          |b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
            (kaiserPacketAngularFrequency c j)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin m)).erase i,
          |b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T) := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [abs_mul]
        exact mul_le_mul (hi j)
          (abs_kaiserPacketReading_offDiagonal_le hc hscale hji.symm)
          (abs_nonneg _) (by positivity)
      _ = (((Finset.univ : Finset (Fin m)).erase i).card : ℝ) *
          (|b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
        simp
      _ ≤ (m : ℝ) * (|b i| *
          (8 * Real.exp (-(Real.sqrt c / 2)) * T)) := by
        apply mul_le_mul_of_nonneg_right
        · have hcard :
            ((Finset.univ : Finset (Fin m)).erase i).card ≤
              (Finset.univ : Finset (Fin m)).card := Finset.card_erase_le
          simp only [Finset.card_univ, Fintype.card_fin] at hcard
          exact_mod_cast hcard
        · positivity
  have hoffSmall : |E| ≤ |b i| * T / 4 := by
    refine hoff.trans ?_
    calc
      (m : ℝ) * (|b i| * (8 * Real.exp (-(Real.sqrt c / 2)) * T)) =
          (32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2))) * (|b i| * T / 4) := by
        ring
      _ ≤ 1 * (|b i| * T / 4) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = |b i| * T / 4 := one_mul _
  have hsplit : b i * D + E = kaiserPacketRow c b i := by
    change b i * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c i) +
      (∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
        b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
          (kaiserPacketAngularFrequency c j)) =
      ∑ j, b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j)
    exact Finset.add_sum_erase (Finset.univ : Finset (Fin m))
      (fun j => b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j)) (Finset.mem_univ i)
  have htriangle : |b i * D| - |E| ≤ |kaiserPacketRow c b i| := by
    calc
      |b i * D| - |E| = |b i * D| - |-E| := by rw [abs_neg]
      _ ≤ |b i * D - -E| := abs_sub_abs_le_abs_sub _ _
      _ = |kaiserPacketRow c b i| := by rw [sub_neg_eq_add, hsplit]
  change |b i| * T / 4 ≤ _
  linarith

theorem kaiserCosTrial_packetFrequency_eq {m : ℕ} (c x : ℝ) (j : Fin m) :
    kaiserCosTrial c (kaiserPacketFrequency c j) x =
      kaiserTrial c x * Real.cos (kaiserPacketAngularFrequency c j * x) := by
  rw [kaiserCosTrial, kaiserPacketFrequency]
  congr 2
  field_simp [Real.pi_ne_zero]

theorem continuous_kaiserGridCombination {m : ℕ} (c : ℝ) (b : Fin m → ℝ) :
    Continuous (kaiserGridCombination c b) :=
  continuous_kaiserCosCombination c (kaiserPacketFrequency c) b

/-- Applying a packet row is exactly integration against its cosine reporter. -/
theorem integral_kaiserGridCombination_mul_cos_eq_row {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) (i : Fin m) :
    (∫ x in (-1 : ℝ)..1,
      kaiserGridCombination c b x *
        Real.cos (kaiserPacketAngularFrequency c i * x)) =
      kaiserPacketRow c b i := by
  have hterm : ∀ j : Fin m, IntervalIntegrable
      (fun x : ℝ => b j * kaiserCosTrial c (kaiserPacketFrequency c j) x *
        Real.cos (kaiserPacketAngularFrequency c i * x)) volume (-1) 1 := by
    intro j
    exact ((continuous_const.mul
      (continuous_kaiserCosTrial c (kaiserPacketFrequency c j))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable
          (μ := volume) (-1) 1
  change (∫ x in (-1 : ℝ)..1,
      (∑ j, b j * kaiserCosTrial c (kaiserPacketFrequency c j) x) *
        Real.cos (kaiserPacketAngularFrequency c i * x)) =
    ∑ j, b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
      (kaiserPacketAngularFrequency c j)
  have hdistribute : (fun x : ℝ =>
      (∑ j, b j * kaiserCosTrial c (kaiserPacketFrequency c j) x) *
        Real.cos (kaiserPacketAngularFrequency c i * x)) =
      (fun x : ℝ => ∑ j,
        b j * kaiserCosTrial c (kaiserPacketFrequency c j) x *
          Real.cos (kaiserPacketAngularFrequency c i * x)) := by
    funext x
    exact Finset.sum_mul
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun j => b j * kaiserCosTrial c (kaiserPacketFrequency c j) x)
      (a := Real.cos (kaiserPacketAngularFrequency c i * x))
  rw [hdistribute, intervalIntegral.integral_finsetSum (fun j _ => hterm j)]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∫ x in (-1 : ℝ)..1,
        b j * kaiserCosTrial c (kaiserPacketFrequency c j) x *
          Real.cos (kaiserPacketAngularFrequency c i * x)) =
        ∫ x in (-1 : ℝ)..1, b j *
          (kaiserCosTrial c (kaiserPacketFrequency c j) x *
            Real.cos (kaiserPacketAngularFrequency c i * x)) := by
      congr 1
      funext x
      ring
    _ = b j * (∫ x in (-1 : ℝ)..1,
        kaiserCosTrial c (kaiserPacketFrequency c j) x *
          Real.cos (kaiserPacketAngularFrequency c i * x)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = b j * kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j) := by
      congr 1
      rw [kaiserPacketReading]
      simp_rw [kaiserCosTrial_packetFrequency_eq]

/-- One packet reading is controlled by twice the physical energy of the combination. -/
theorem kaiserPacketRow_sq_le_two_mul_energy {m : ℕ}
    (c : ℝ) (b : Fin m → ℝ) (i : Fin m) :
    kaiserPacketRow c b i ^ (2 : ℕ) ≤
      2 * ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ (2 : ℕ) := by
  let f : ℝ → ℝ := kaiserGridCombination c b
  let g : ℝ → ℝ := fun x => Real.cos (kaiserPacketAngularFrequency c i * x)
  have hfcont : Continuous f := continuous_kaiserGridCombination c b
  have hgcont : Continuous g :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hfsq : Integrable (fun x => f x ^ (2 : ℕ)) (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (hfcont.pow 2).integrableOn_Ioc
  have hgsq : Integrable (fun x => g x ^ (2 : ℕ)) (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (hgcont.pow 2).integrableOn_Ioc
  have hcs := _root_.HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    (μ := volume.restrict (Ioc (-1 : ℝ) 1))
    hfcont.aestronglyMeasurable hgcont.aestronglyMeasurable hfsq hgsq
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  rw [← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_of_le hle] at hcs
  have hgBound : (∫ x in (-1 : ℝ)..1, g x ^ (2 : ℕ)) ≤ 2 := by
    have hgInt : IntervalIntegrable (fun x => g x ^ (2 : ℕ)) volume (-1) 1 :=
      (hgcont.pow 2).intervalIntegrable (μ := volume) (-1) 1
    have honeInt : IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume (-1) 1 :=
      intervalIntegrable_const
    calc
      (∫ x in (-1 : ℝ)..1, g x ^ (2 : ℕ)) ≤ ∫ _x in (-1 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hle hgInt honeInt
        intro x _
        dsimp only [g]
        nlinarith [Real.neg_one_le_cos (kaiserPacketAngularFrequency c i * x),
          Real.cos_le_one (kaiserPacketAngularFrequency c i * x)]
      _ = 2 := by norm_num
  have henergy0 : 0 ≤ ∫ x in (-1 : ℝ)..1, f x ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hle fun _ _ => sq_nonneg _
  have hrow : (∫ x in (-1 : ℝ)..1, f x * g x) = kaiserPacketRow c b i := by
    exact integral_kaiserGridCombination_mul_cos_eq_row c b i
  rw [hrow] at hcs
  change kaiserPacketRow c b i ^ (2 : ℕ) ≤ 2 * ∫ x in (-1 : ℝ)..1, f x ^ (2 : ℕ)
  calc
    kaiserPacketRow c b i ^ (2 : ℕ) ≤
        (∫ x in (-1 : ℝ)..1, f x ^ (2 : ℕ)) * (∫ x in (-1 : ℝ)..1, g x ^ (2 : ℕ)) := hcs
    _ ≤ (∫ x in (-1 : ℝ)..1, f x ^ (2 : ℕ)) * 2 :=
      mul_le_mul_of_nonneg_left hgBound henergy0
    _ = 2 * ∫ x in (-1 : ℝ)..1, f x ^ (2 : ℕ) := by ring

/-- Uniform physical-energy lower bound for every vector in the conditioned packet span. -/
theorem exp_sq_mul_coeffEnergy_le_kaiserGridEnergy {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c)
    (hsmall : 32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2)) ≤ 1)
    (b : Fin m → ℝ) :
    (∑ j, b j ^ (2 : ℕ)) * Real.exp c ^ (2 : ℕ) ≤
      128 * (m : ℝ) * c ^ (2 : ℕ) *
        (∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ (2 : ℕ)) := by
  obtain ⟨i, hi⟩ := exists_max_abs_kaiserPacketCoefficient hm b
  let T : ℝ := kaiserAngularTransform c 0
  let E : ℝ := ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ (2 : ℕ)
  have hT : Real.exp c / (2 * c) ≤ T :=
    exp_div_two_c_le_kaiserAngularTransform_zero hc
  have hT0 : 0 ≤ T := (kaiserAngularTransform_zero_pos (one_pos.trans_le hc)).le
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hcoeff := sum_sq_kaiserPacketCoefficient_le b i hi
  have hrow := abs_kaiserPacketRow_ge hc hscale hsmall b i hi
  change |b i| * T / 4 ≤ |kaiserPacketRow c b i| at hrow
  have hrowCS : kaiserPacketRow c b i ^ (2 : ℕ) ≤ 2 * E :=
    kaiserPacketRow_sq_le_two_mul_energy c b i
  have hleft0 : 0 ≤ |b i| * T / 4 := by positivity
  have hrowSq := pow_le_pow_left₀ hleft0 hrow 2
  rw [sq_abs] at hrowSq
  have henergy0 : 0 ≤ E :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  change (∑ j, b j ^ (2 : ℕ)) * Real.exp c ^ (2 : ℕ) ≤ 128 * (m : ℝ) * c ^ (2 : ℕ) * E
  have hTscaled : Real.exp c ≤ 2 * c * T := by
    have hcpos : 0 < 2 * c := by positivity
    simpa [mul_comm] using (div_le_iff₀ hcpos).mp hT
  have hexpSq := pow_le_pow_left₀ (Real.exp_pos c).le hTscaled 2
  have hcombined := hrowSq.trans hrowCS
  have haT : |b i| ^ (2 : ℕ) * T ^ (2 : ℕ) ≤ 32 * E := by
    nlinarith
  have hcoeffT := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hST : (∑ j, b j ^ (2 : ℕ)) * T ^ (2 : ℕ) ≤ 32 * (m : ℝ) * E := by
    calc
      (∑ j, b j ^ (2 : ℕ)) * T ^ (2 : ℕ) ≤ ((m : ℝ) * |b i| ^ (2 : ℕ)) * T ^ (2 : ℕ) := hcoeffT
      _ = (m : ℝ) * (|b i| ^ (2 : ℕ) * T ^ (2 : ℕ)) := by ring
      _ ≤ (m : ℝ) * (32 * E) :=
        mul_le_mul_of_nonneg_left haT (Nat.cast_nonneg m)
      _ = 32 * (m : ℝ) * E := by ring
  have hcoeff0 : 0 ≤ ∑ j, b j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  calc
    (∑ j, b j ^ (2 : ℕ)) * Real.exp c ^ (2 : ℕ) ≤
        (∑ j, b j ^ (2 : ℕ)) * (2 * c * T) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hexpSq hcoeff0
    _ = 4 * c ^ (2 : ℕ) * ((∑ j, b j ^ (2 : ℕ)) * T ^ (2 : ℕ)) := by ring
    _ ≤ 4 * c ^ (2 : ℕ) * (32 * (m : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hST (by positivity)
    _ = 128 * (m : ℝ) * c ^ (2 : ℕ) * E := by ring

end GaloisForLFunctions.RHTower

end
