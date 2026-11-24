import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginSelectedCycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JointGraphDeterminant

/-! An origin coefficient supported at fixed points extends from the
origin equations to the joint graph and origin Čech–Koszul complex. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.WH

variable {k F E L κ : Type} [Field k] [CharZero k] [IsAlgClosed k]
  [Field F] [Field E] [Field L] [LinearOrder κ] [Fintype κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d p q : ℕ} {x : Fin (d + 1) → F} {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}
  (h : IsPd k x) (j₂ : E →ₐ[k] L)

local notation "G" => κ ⊕ₗ DiagonalIndex d
local notation "Q" => (κ ⊕ₗ DiagonalIndex d) ⊕ₗ Fin d
local notation "T" => graphChartSystem h j₂ q p
local notation "B₀" => rB k L x {0}
local notation "B" => RY x j₂ {0} {0}
local notation "nG" => (appendedDiagonalDegrees (d := d) n : G → ℕ × ℕ)
local notation "zG" => graphScalarMap (IsScalarTower.toAlgHom k E L) j₂ ∘ appendedDiagonalWeights h q p z
local notation "nQ" => (jointDegrees (d := d) (nG) : Q → ℕ × ℕ)
local notation "zQ" => WeightedChartSystem.jointWeights (T) (zG)

/-- A coefficient supported on the fixed part of the origin fibre
gives a joint cocycle with the prescribed signed origin value. -/
theorem exists_originSupportedJointGraphCocycle
    (hL : IsFinCover k L x) (hqp : q + p = d)
    [IsReduced (B₀ ⧸ originIdeal k L x)] [Algebra.FiniteType k B]
    (hz : NormalizedDiagonalEquations h n z)
    (horigin : ∀ e : B →ₐ[k] k,
      (∀ l, e ⟨_, originAffineWeight_mem h j₂ (Finset.mem_singleton_self 0)
        (Finset.mem_singleton_self 0) l⟩ = 0) →
      ∃ f : OriginFibrePoint k L x, ∀ a b, Val B e a b ↔ Val B₀ f.1 a b)
    (hex : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → ∀ m < (d : ℤ),
      ((T).columnComplex nQ zQ I J).Z m ≤ ((T).columnComplex nQ zQ I J).B m)
    (hoff : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → (I ≠ {0} ∨ J ≠ {0}) →
      ((T).columnComplex nQ zQ I J).Z (d : ℤ) ≤ ((T).columnComplex nQ zQ I J).B (d : ℤ))
    (b : B₀) (hb : ∀ f : OriginFibrePoint k L x,
      ¬ IsFix B₀ f.1 j₂ (rB k E x {0}) → f.1 b = 0) :
    ∃ c ∈ ((T).complex nQ zQ).Z ((d : ℤ) + 2),
      ((T).scaleColumn nQ 0 0).symm (fun K => c (uni (uni {0} {0}) K))
        (selectedIndices (jointOriginSelection (κ := κ))) =
          (-1 : k) ^ d • ((b : L) • originAffineVolume k L x) ∧
      ∀ (i j : Fin (d + 1)) (K : Finset Q), i ≠ 0 ∨ j ≠ 0 → K.card = d →
        c (uni (uni {i} {j}) K) = 0 := by
  classical
  let hT := graphChartSystem_good h j₂ q p
  let hG := graphChartSystem_admitted_map h j₂ q p nG _
    (appendedDiagonal_admitted h q p hz)
  let hQ := (T).jointWeights_admitted hT hG
  let h₀ : (0 : Fin (d + 1)) ∈ ({0} : Finset (Fin (d + 1))) := Finset.mem_singleton_self 0
  let r : Q → B := graphColumnWeights h j₂ (q := q) (p := p) h₀ h₀ hQ
  let sel : Fin d ↪o Q := jointOriginSelection
  let inc : B₀ →ₐ[k] B := Subalgebra.inclusion le_sup_left
  let eps : k := (-1 : k) ^ d
  let a : B := algebraMap k B eps * inc b
  have hsign : (a : L) • originAffineVolume k L x =
      eps • ((b : L) • originAffineVolume k L x) := by
    change (algebraMap k L eps * (b : L)) • originAffineVolume k L x = _
    rw [mul_smul, IsScalarTower.algebraMap_smul L]
  have hmodel (e : B →ₐ[k] k) (he : ∀ l, e (r (sel l)) = 0) :
      ∃ f : OriginFibrePoint k L x, ∀ a b, Val B e a b ↔ Val B₀ f.1 a b := by
    apply horigin e
    intro l
    have hr := graphColumnWeights_joint_right h j₂ h₀ h₀ hG l
    exact (congrArg e hr).symm.trans (he l)
  have hsel (l : Fin d) : (r (sel l) : L) = algebraMap F L (x l.succ / x 0) := by
    have hr := congrArg (fun u : B => (u : L)) (graphColumnWeights_joint_right h j₂ h₀ h₀ hG l)
    exact hr.trans (graphColumnWeights_leftOrigin h j₂ (q := q) (p := p) h₀ h₀ l)
  have hvol : originAffineVolume k L x ∈ omB k L B d :=
    omB_mono (show B₀ ≤ B from le_sup_left) d originAffineVolume_mem
  have hann (e : B →ₐ[k] k) (he : ∀ l, e (r (sel l)) = 0)
      (l : Q) (hl : l ∉ selectedIndices sel) : e (r l) * e a = 0 := by
    obtain ⟨f, hval⟩ := hmodel e he
    by_cases hf : IsFix B₀ f.1 j₂ (rB k E x {0})
    · obtain ⟨l, rfl⟩ := (toLex : G ⊕ Fin d ≃ Q).surjective l
      rcases l with m | m
      · have hrl : (r (joinedLeft (κ := Fin d) m) : L) =
            graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) m :=
          congrArg (fun u : B => (u : L)) (graphColumnWeights_joint_left h j₂ h₀ h₀ hG m)
        have hv := val_graphAffineWeight_at_fixedOrigin h j₂ hz f hf m
        have hv' := (hval _ _).mpr (hrl.symm ▸ hv)
        have he₀ := val_value_unique B e (val_chartElement B e (r (joinedLeft (κ := Fin d) m))) hv'
        change e (r (joinedLeft (κ := Fin d) m)) * e a = 0
        rw [he₀, zero_mul]
      · exact (hl (Finset.mem_map.mpr ⟨m, Finset.mem_univ _, rfl⟩)).elim
    · have he' : e (inc b) = f.1 b :=
        val_value_unique B e (val_chartElement B e (inc b))
          ((hval _ _).mpr (val_chartElement B₀ f.1 b))
      change e (r l) * e (algebraMap k B eps * inc b) = 0
      rw [map_mul, he', hb f hf, mul_zero, mul_zero]
  obtain ⟨u, hu, hu₀⟩ := exists_chartKoszulCycle_of_originValue hL B r sel hmodel hsel hvol a hann
  let sc := (T).scaleColumn nQ 0 0
  have hu' := (graphColumn_scale_mem_cycles_iff h j₂ hqp h₀ h₀ hQ d u).mpr hu
  obtain ⟨c, hc, hc₀⟩ := (T).exists_originSupportedCocycle hT hQ hex hoff hu'
  refine ⟨c, hc, ?_, ?_⟩
  · let S := selectedIndices sel
    have hS : S.card = d := by simp [S, selectedIndices]
    have he := hc₀ 0 0 S hS
    rw [if_pos ⟨rfl, rfl⟩] at he
    change (sc.symm (fun K => c (uni (uni {0} {0}) K))) S =
      eps • ((b : L) • originAffineVolume k L x)
    calc
      _ = (sc.symm (sc u)) S := by
        change (T).act (((T).normalizationProduct nQ 0 0 S)⁻¹ : Lˣ) (c (uni (uni {0} {0}) S)) =
          (T).act (((T).normalizationProduct nQ 0 0 S)⁻¹ : Lˣ) ((sc u) S)
        rw [he]
      _ = _ := by rw [sc.symm_apply_apply, hu₀, hsign]
  · intro i j K hij hK
    exact (hc₀ i j K hK).trans (if_neg (fun h => hij.elim (fun hi => hi h.1) fun hj => hj h.2))

end GlobalTheory.WH
