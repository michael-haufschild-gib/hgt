import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.StepPacketMassAndGroundEnergy
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# The binding energy of a window is carried by its floor trees

On step packets the neutral part is the archimedean form minus the contacts:
`A(0) h(0) + ∫_0^∞ 2ω(x)(h(0) − h(x)) dx − 2 Σ_k Λ(k) k^{−1/2} h(log k)`, with `h` the
autocorrelation of the packet, `ω > 0` the Lévy density of the Gamma factor and
`A(0) = −(γ + π/2 + log 8π)`.

* **Without the floor trees no window binds beyond the archimedean constant**
  (`sum_neutralBlock_one_ge`, `le_eigenvalue_of_prime_free`). The jump integral is nonnegative,
  because `h(x) ≤ h(0)` (`packetAutocorr_le_zero`). So on every window, at every block size, the
  neutral part without contacts is at least `A(0)` times the mass, and its binding energy is at
  most `γ + π/2 + log 8π < 5.4`.
* **The tree of `k` adds at most `2Λ(k)/√k`** (`sum_contact_le`). Its edges form a
  `k`-to-one matching from the children to the parents; a parent has at most `k` children and a
  child one parent, and the weighted Schur test with weights `1/√k` and `√k` bounds the contact
  form by `2√k` times the mass.

Hence (`le_eigenvalue_of_contacts`) the binding energy of every window with contacts up to `Q`
is at most `γ + π/2 + log 8π + 2 Σ_{2 ≤ k ≤ Q} Λ(k)/√k`, a Chebyshev sum of order `√Q`.
Together with the lower bound from the root block, the binding energy of a window of ratio `ρ`
has the order `√ρ` up to a logarithm, unconditionally, and all of it but a bounded part is
created by the floor trees.
-/

open Finset Matrix MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The jump integral is nonnegative -/

/-- **The autocorrelation is largest at zero**: `h(x) ≤ h(0)` by `2ab ≤ a² + b²` and the
translation invariance of the integral. -/
theorem packetAutocorr_le_zero {f : ℝ → ℝ} {x : ℝ}
    (hprod : Integrable fun u => f u * f (u + x)) (hsq : Integrable fun u => f u ^ 2) :
    packetAutocorr f x ≤ packetAutocorr f 0 := by
  have hshift : Integrable fun u => f (u + x) ^ 2 := hsq.comp_add_right x
  have hbound : Integrable fun u => (f u ^ 2 + f (u + x) ^ 2) / 2 := (hsq.add hshift).div_const 2
  have h0 : packetAutocorr f 0 = ∫ u, f u ^ 2 := by
    unfold packetAutocorr
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
  have htrans : ∫ u, f (u + x) ^ 2 = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) x
  calc packetAutocorr f x = ∫ u, f u * f (u + x) := rfl
    _ ≤ ∫ u, (f u ^ 2 + f (u + x) ^ 2) / 2 :=
        integral_mono hprod hbound fun u => by
          nlinarith [sq_nonneg (f u - f (u + x))]
    _ = ((∫ u, f u ^ 2) + ∫ u, f (u + x) ^ 2) / 2 := by
        rw [integral_div, integral_add hsq hshift]
    _ = packetAutocorr f 0 := by rw [htrans, h0]; ring

/-- The autocorrelation integrand of a step packet is integrable. -/
theorem integrable_stepPacket_mul_shift (R J : ℕ) (σ : ℕ → ℝ) (x : ℝ) :
    Integrable fun u => stepPacket R J σ u * stepPacket R J σ (u + x) := by
  have hexp : (fun u => stepPacket R J σ u * stepPacket R J σ (u + x)) =
      fun u => ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u *
          flatPacket ((R + l : ℕ) : ℝ) ((R + (l + 1) : ℕ) : ℝ) (u + x)) := by
    funext u
    simp only [stepPacket]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (integrable_flatPacket_mul_flatPacket _ _ _ _ x).const_mul _

/-- **The jump density of a step packet is nonnegative.** -/
theorem levyJump_stepPacket_nonneg (R J : ℕ) (σ : ℕ → ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ levyJump (stepPacket R J σ) x := by
  have hsq : Integrable fun u => stepPacket R J σ u ^ 2 := by
    have h := integrable_stepPacket_mul_shift R J σ 0
    simpa [sq] using h
  have hle := packetAutocorr_le_zero (integrable_stepPacket_mul_shift R J σ x) hsq
  have hω := _root_.RHTower.archLevyDensity_pos hx
  unfold levyJump
  nlinarith [mul_nonneg hω.le (sub_nonneg.mpr hle)]

/-! ### Without the floor trees -/

/-- **Without the floor trees the neutral part of a window is at least the archimedean constant
times the mass**, at every block size. -/
theorem sum_neutralBlock_one_ge {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    EF.gammaBracket 0 * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock 1 (R + j) (R + l) := by
  have h21 : Finset.Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
  rw [← neutralForm_stepPacket hR 1 J σ, neutralForm_eq, h21, Finset.sum_empty, mul_zero,
    sub_zero, packetAutocorr_stepPacket_zero hR J σ]
  have hjump : 0 ≤ ∫ x in Set.Ioi 0, levyJump (stepPacket R J σ) x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => levyJump_stepPacket_nonneg R J σ hx
  linarith

/-- The archimedean constant: `−A(0) = γ + π/2 + log 8π`. -/
theorem neg_gammaBracket_zero :
    -EF.gammaBracket 0 = Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
  rw [_root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq, neg_neg]

/-- **A window without floor trees binds at most `γ + π/2 + log 8π`**: the eigenvalue of a
positive eigenvector of its neutral part is at least `A(0)`. -/
theorem le_eigenvalue_of_prime_free {R J : ℕ} (hR : 1 ≤ R) (hJ : 1 ≤ J) {φ : Fin J → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : neutralWindow 1 R J *ᵥ φ = lam • φ) :
    EF.gammaBracket 0 ≤ lam := by
  have hform := sum_neutralBlock_one_ge hR J (extendFin φ)
  have hb : bilin (neutralWindow 1 R J) φ φ =
      ∑ j ∈ range J, ∑ l ∈ range J,
        extendFin φ j * extendFin φ l * neutralBlock 1 (R + j) (R + l) :=
    sum_fin_windowMatrix_eq (neutralBlock 1) R φ
  have hmass : ∑ j ∈ range J, extendFin φ j ^ 2 = ∑ k, φ k * φ k := by
    rw [show ∑ k, φ k * φ k = ∑ j ∈ range J, extendFin (fun k => φ k * φ k) j from
      sum_fin_eq_sum_range_extendFin _]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [extendFin, dif_pos (Finset.mem_range.mp hj), sq]
  have hpos : 0 < ∑ k, φ k * φ k :=
    Finset.sum_pos (fun k _ => mul_pos (hφ k) (hφ k)) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  rw [← hb, bilin_eigen heig, hmass] at hform
  exact le_of_mul_le_mul_right hform hpos

/-! ### What one floor tree adds -/

/-- The neutral part is the neutral part without floor trees minus the contacts. -/
theorem neutralBlock_eq_one_sub (Q a b : ℕ) :
    neutralBlock Q a b = neutralBlock 1 a b - floorContact Q (min a b) (max a b) := by
  have h21 : Finset.Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
  have h1 : floorContact 1 (min a b) (max a b) = 0 := by
    simp only [floorContact, h21, Finset.sum_empty]
  simp only [neutralBlock, blockMatrix, h1]
  ring

/-- A block has at most one parent under the floor map of `k`. -/
theorem sum_parent_le_one (R k J l : ℕ) :
    ∑ j ∈ range J, (if (R + l) / k = R + j then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (Finset.filter (fun j => (R + l) / k = R + j) (range J)).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact Nat.add_left_cancel (ha.2.symm.trans hb.2)
  exact_mod_cast this

/-- A block has at most `k` children under the floor map of `k`. -/
theorem sum_children_le (R k J j : ℕ) (hk : 1 ≤ k) :
    ∑ l ∈ range J, (if (R + l) / k = R + j then (1 : ℝ) else 0) ≤ k := by
  rw [Finset.sum_boole]
  have hsub : Finset.filter (fun l => (R + l) / k = R + j) (range J) ⊆
      Finset.Ico ((R + j) * k - R) ((R + j) * k - R + k) := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    have h1 : (R + l) / k * k ≤ R + l := Nat.div_mul_le_self _ _
    have h2 : R + l < (R + l) / k * k + k := Nat.lt_div_mul_add (by omega)
    rw [hl.2] at h1 h2
    generalize (R + j) * k = T at h1 h2 ⊢
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at this
  exact_mod_cast this

/-- **The contact form of the floor map of `k` is at most `2√k` times the mass**: twice the
sum over parent–child pairs, bounded by the weighted Schur test. -/
theorem sum_floorMap_le (R J k : ℕ) (hR : 1 ≤ R) (hk : 2 ≤ k) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) ≤
      2 * Real.sqrt k * ∑ j ∈ range J, σ j ^ 2 := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have hsk2 : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  -- the symmetric indicator is the parent–child indicator in both orders
  set P : ℕ → ℕ → ℝ := fun j l => if (R + l) / k = R + j then 1 else 0 with hP
  have hsplit : ∀ j l, (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) =
      P j l + P l j := by
    intro j l
    simp only [hP]
    rcases lt_trichotomy j l with hjl | hjl | hjl
    · rw [max_eq_right (by omega), min_eq_left (by omega)]
      have : ¬ (R + j) / k = R + l := fun h => by
        have h' := Nat.div_le_self (R + j) k
        rw [h] at h'
        omega
      rw [if_neg this, add_zero]
    · subst hjl
      have : ¬ (R + j) / k = R + j := fun h => by
        have h' := Nat.div_lt_self (show 0 < R + j by omega) (show 1 < k by omega)
        rw [h] at h'
        exact lt_irrefl _ h'
      rw [max_self, min_self, if_neg this, add_zero]
    · rw [max_eq_left (by omega), min_eq_right (by omega)]
      have : ¬ (R + l) / k = R + j := fun h => by
        have h' := Nat.div_le_self (R + l) k
        rw [h] at h'
        omega
      rw [if_neg this, zero_add]
  have hP0 : ∀ j l, 0 ≤ P j l := fun j l => by simp only [hP]; split_ifs <;> norm_num
  have hswap : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P l j =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hpair : ∀ j l, 2 * (σ j * σ l * P j l) ≤
      P j l * (σ j ^ 2 / Real.sqrt k) + P j l * (Real.sqrt k * σ l ^ 2) := by
    intro j l
    have key : 2 * (σ j * σ l) ≤ σ j ^ 2 / Real.sqrt k + Real.sqrt k * σ l ^ 2 := by
      have e : σ j ^ 2 / Real.sqrt k + Real.sqrt k * σ l ^ 2 - 2 * (σ j * σ l) =
          (σ j - Real.sqrt k * σ l) ^ 2 / Real.sqrt k := by
        field_simp
        ring
      have : 0 ≤ (σ j - Real.sqrt k * σ l) ^ 2 / Real.sqrt k :=
        div_nonneg (sq_nonneg _) hsk.le
      linarith
    have := mul_le_mul_of_nonneg_left key (hP0 j l)
    nlinarith
  have hparents : ∑ j ∈ range J, ∑ l ∈ range J, P j l * (Real.sqrt k * σ l ^ 2) ≤
      Real.sqrt k * ∑ l ∈ range J, σ l ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.sum_mul]
    have := sum_parent_le_one R k J l
    have hnn : 0 ≤ Real.sqrt k * σ l ^ 2 := mul_nonneg hsk.le (sq_nonneg _)
    calc (∑ j ∈ range J, P j l) * (Real.sqrt k * σ l ^ 2) ≤ 1 * (Real.sqrt k * σ l ^ 2) :=
          mul_le_mul_of_nonneg_right this hnn
      _ = Real.sqrt k * σ l ^ 2 := one_mul _
  have hchildren : ∑ j ∈ range J, ∑ l ∈ range J, P j l * (σ j ^ 2 / Real.sqrt k) ≤
      Real.sqrt k * ∑ j ∈ range J, σ j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    have := sum_children_le R k J j (by omega)
    have hnn : 0 ≤ σ j ^ 2 / Real.sqrt k := div_nonneg (sq_nonneg _) hsk.le
    calc (∑ l ∈ range J, P j l) * (σ j ^ 2 / Real.sqrt k) ≤ k * (σ j ^ 2 / Real.sqrt k) :=
          mul_le_mul_of_nonneg_right this hnn
      _ = σ j ^ 2 * ((k : ℝ) / Real.sqrt k) := by ring
      _ = Real.sqrt k * σ j ^ 2 := by rw [Real.div_sqrt]; ring
  have hsum : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
      (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) =
      2 * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l := by
    simp only [hsplit, mul_add, Finset.sum_add_distrib, hswap]
    ring
  rw [hsum]
  have h2 : 2 * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l ≤
      ∑ j ∈ range J, ∑ l ∈ range J,
        (P j l * (σ j ^ 2 / Real.sqrt k) + P j l * (Real.sqrt k * σ l ^ 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => hpair j l
  simp only [Finset.sum_add_distrib] at h2
  linarith

/-- **The contacts of a window are at most `2 Σ_k Λ(k)/√k` times the mass.** -/
theorem sum_contact_le {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) ≤
      2 * (∑ k ∈ Icc 2 Q, (Λ k : ℝ) / Real.sqrt k) * ∑ j ∈ range J, σ j ^ 2 := by
  have hexp : ∀ j l, σ j * σ l * floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / k * (σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)) := by
    intro j l
    simp only [floorContact, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
  simp only [hexp]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm,
    Finset.mul_sum (Icc 2 Q) (fun k => (Λ k : ℝ) / Real.sqrt k) 2, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hw : (0 : ℝ) ≤ (Λ k : ℝ) / k := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le
  have h := sum_floorMap_le R J k hR hk2 σ
  have hpull : ∑ j ∈ range J, ∑ l ∈ range J, (Λ k : ℝ) / k * (σ j * σ l *
      (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)) =
      (Λ k : ℝ) / k * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [hpull]
  calc (Λ k : ℝ) / k * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)
      ≤ (Λ k : ℝ) / k * (2 * Real.sqrt k * ∑ j ∈ range J, σ j ^ 2) :=
        mul_le_mul_of_nonneg_left h hw
    _ = 2 * ((Λ k : ℝ) / Real.sqrt k) * ∑ j ∈ range J, σ j ^ 2 := by
        have e : Real.sqrt k / k = 1 / Real.sqrt k := Real.sqrt_div_self'
        calc (Λ k : ℝ) / k * (2 * Real.sqrt k * ∑ j ∈ range J, σ j ^ 2) =
              2 * (Λ k : ℝ) * (∑ j ∈ range J, σ j ^ 2) * (Real.sqrt k / k) := by ring
          _ = 2 * (Λ k : ℝ) * (∑ j ∈ range J, σ j ^ 2) * (1 / Real.sqrt k) := by rw [e]
          _ = 2 * ((Λ k : ℝ) / Real.sqrt k) * ∑ j ∈ range J, σ j ^ 2 := by ring

/-- **The neutral part with contacts up to `Q` is at least `A(0) − 2 Σ_{k ≤ Q} Λ(k)/√k` times
the mass**, at every block size. -/
theorem sum_neutralBlock_ge {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ) (σ : ℕ → ℝ) :
    (EF.gammaBracket 0 - 2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / Real.sqrt k) *
        ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  have h1 := sum_neutralBlock_one_ge hR J σ
  have h2 := sum_contact_le hR Q J σ
  have hsplit : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock 1 (R + j) (R + l) -
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
          floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [neutralBlock_eq_one_sub]; ring
  rw [hsplit]
  nlinarith

/-- **The binding energy of a window with contacts up to `Q` is at most
`γ + π/2 + log 8π + 2 Σ_{2 ≤ k ≤ Q} Λ(k)/√k`.** -/
theorem le_eigenvalue_of_contacts {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 1 ≤ J) {φ : Fin J → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : neutralWindow Q R J *ᵥ φ = lam • φ) :
    EF.gammaBracket 0 - 2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / Real.sqrt k ≤ lam := by
  have hform := sum_neutralBlock_ge hR Q J (extendFin φ)
  have hb : bilin (neutralWindow Q R J) φ φ =
      ∑ j ∈ range J, ∑ l ∈ range J,
        extendFin φ j * extendFin φ l * neutralBlock Q (R + j) (R + l) :=
    sum_fin_windowMatrix_eq (neutralBlock Q) R φ
  have hmass : ∑ j ∈ range J, extendFin φ j ^ 2 = ∑ k, φ k * φ k := by
    rw [show ∑ k, φ k * φ k = ∑ j ∈ range J, extendFin (fun k => φ k * φ k) j from
      sum_fin_eq_sum_range_extendFin _]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [extendFin, dif_pos (Finset.mem_range.mp hj), sq]
  have hpos : 0 < ∑ k, φ k * φ k :=
    Finset.sum_pos (fun k _ => mul_pos (hφ k) (hφ k)) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  rw [← hb, bilin_eigen heig, hmass] at hform
  exact le_of_mul_le_mul_right hform hpos

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
