import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphCoordinateColumnTests
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginJointCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RightOriginChart

/-! The graph class and the logarithmic origin class are the two
restrictions of a joint cocycle up to mixed Čech boundaries. -/

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

local notation "ι" => Fin (d + 1)
local notation "G" => κ ⊕ₗ DiagonalIndex d
local notation "Q" => (κ ⊕ₗ DiagonalIndex d) ⊕ₗ Fin d
local notation "T" => graphChartSystem h j₂ q p
local notation "B₀" => rB k L x {0}
local notation "B" => fun I J => RY x j₂ I J
local notation "Fixed" => fun f : OriginFibrePoint k L x => IsFix B₀ (Subtype.val f) j₂ (rB k E x {0})
local notation "nG" => (appendedDiagonalDegrees (d := d) n : G → ℕ × ℕ)
local notation "zG" => graphScalarMap (IsScalarTower.toAlgHom k E L) j₂ ∘ appendedDiagonalWeights h q p z
local notation "nT" => (fun _ : Fin d => ((1, 0) : ℕ × ℕ))
local notation "nQ" => (jointDegrees (d := d) (nG) : Q → ℕ × ℕ)
local notation "zQ" => WeightedChartSystem.jointWeights (T) (zG)

/-- If the normalized graph residues match those of an origin
coefficient supported on the fixed points, the graph projection
is cohomologous to the left edge of that origin volume. -/
theorem chartPart_graph_sub_origin_mem_boundary
    (hL : IsFinCover k L x) (hqp : q + p = d) [IsReduced (B₀ ⧸ originIdeal k L x)]
    (hz : NormalizedDiagonalEquations h n z)
    (hfinite : ∀ I J : Finset ι, I.Nonempty → J.Nonempty → Algebra.FiniteType k ((B) I J))
    (hgraph : ∀ (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) (e : (B) I J →ₐ[k] k),
      (∀ l, e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0) →
      I = {0} ∧ J = {0} ∧
        ∃ f : OriginFibrePoint k L x, (Fixed) f ∧
          ∀ a b, Val ((B) I J) e a b ↔ Val B₀ f.1 a b)
    (horigin : ∀ (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) (e : (B) I J →ₐ[k] k),
      (∀ l, e ⟨_, originAffineWeight_mem h j₂ hi hj l⟩ = 0) →
      I = {0} ∧ ∃ f : OriginFibrePoint k L x, ∀ a b, Val ((B) I J) e a b ↔ Val B₀ f.1 a b)
    (A : OriginFibrePoint k L x → Matrix (Fin d) (Fin d) k)
    (hrow : ∀ f, (Fixed) f → ∀ m, ∃ (c : B₀) (g : Fin d → B₀), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * A f m l)
    (hdet : ∀ f, (Fixed) f → (1 - A f).det ≠ 0)
    (b : B₀) (hb : ∀ f, ¬ (Fixed) f → f.1 b = 0)
    {g : Finset (ChartPair d ⊕ₗ G) → DR k L}
    (hg : g ∈ ((T).complex nG (zG)).Z ((d : ℤ) + 2))
    (hvalue : ∀ f, (Fixed) f → ∃ s : L,
      ((T).scaleColumn nG 0 0).symm (fun K => g (uni (uni {0} {0}) K))
        (selectedIndices (graphOriginSelection (κ := κ))) =
          (-1 : k) ^ d • (s • originAffineVolume k L x) ∧
      Val B₀ f.1 s ((1 - A f).det * f.1 b)) :
    chartPart g - edge1 (originVolumeCochain b) ∈ (mixedCech (T).M).B ((d : ℤ) + 2) := by
  classical
  let hT := graphChartSystem_good h j₂ q p
  let hG := graphChartSystem_admitted_map h j₂ q p nG _
    (appendedDiagonal_admitted h q p hz)
  let hO := (T).leftOriginWeights_admitted hT
  let hQ := (T).jointWeights_admitted hT hG
  let eG : G ↪o Q := joinedLeft
  let eO : Fin d ↪o Q := joinedRight
  let sG := selectedIndices (graphOriginSelection (κ := κ) (d := d))
  let sQ := selectedIndices (jointGraphSelection (κ := κ) (d := d))
  let sO := selectedIndices (jointOriginSelection (κ := κ) (d := d))
  have hSG : sG.map eG.toEmbedding = sQ := by
    simp only [sG, sQ, selectedIndices, Finset.map_map] <;> rfl
  have hSO : Finset.univ.map eO.toEmbedding = sO := rfl
  have hGTests (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) :=
    letI := hfinite I J ⟨i, hi⟩ ⟨j, hj⟩
    graphColumn_tests_of_fixedOrigin h j₂ hqp hL hi hj hz A hrow hdet (hgraph I J hi hj)
  have hOTests (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) :=
    letI := hfinite I J ⟨i, hi⟩ ⟨j, hj⟩
    graphColumn_tests_of_originCoordinates h j₂ hqp hL hi hj hO (OrderEmbedding.id _)
      (graphColumnWeights_leftOrigin h j₂ (q := q) (p := p) hi hj)
      (fun e he => by
        obtain ⟨hI, f, hval⟩ := horigin I J hi hj e he
        exact ⟨Finset.mem_singleton.mp (hI ▸ hi), f, hval⟩)
  have hQTests (I J : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ J) :=
    letI := hfinite I J ⟨i, hi⟩ ⟨j, hj⟩
    graphColumn_tests_of_originCoordinates h j₂ hqp hL hi hj hQ (jointOriginSelection (κ := κ))
      (fun l => (congrArg (fun u : (B) I J => (u : L))
        (graphColumnWeights_joint_right h j₂ hi hj hG l)).trans
        (graphColumnWeights_leftOrigin h j₂ (q := q) (p := p) hi hj l))
      (fun e he => by
        have heO (l : Fin d) :
            e ⟨_, originAffineWeight_mem h j₂ hi hj l⟩ = 0 :=
          (congrArg e (graphColumnWeights_joint_right h j₂ hi hj hG l)).symm.trans (he (eO l))
        obtain ⟨hI, f, hval⟩ := horigin I J hi hj e heO
        exact ⟨Finset.mem_singleton.mp (hI ▸ hi), f, hval⟩)
  have hoff (I J : Finset ι) (hI : I.Nonempty) (hJ : J.Nonempty) (hij : I ≠ {0} ∨ J ≠ {0}) :
      ((T).columnComplex nQ zQ I J).Z (d : ℤ) ≤ ((T).columnComplex nQ zQ I J).B (d : ℤ) := by
    have hi := chartIndex_mem hI
    have hj := chartIndex_mem hJ
    intro c hc
    refine (hQTests I J hi hj).2 c hc (fun e he => ?_)
    have heG (l : G) : e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0 :=
      (congrArg e (graphColumnWeights_joint_left h j₂ hi hj hG l)).symm.trans (he (eG l))
    obtain ⟨heI, heJ, _⟩ := hgraph I J hi hj e heG
    exact False.elim (hij.elim (fun hn => hn heI) fun hn => hn heJ)
  let h₀ : (0 : ι) ∈ ({0} : Finset ι) := Finset.mem_singleton_self 0
  letI : Algebra.FiniteType k ((B) {0} {0}) :=
    hfinite {0} {0} (Finset.singleton_nonempty 0) (Finset.singleton_nonempty 0)
  obtain ⟨u, hu, huO, huOff⟩ := exists_originSupportedJointGraphCocycle h j₂ hL hqp hz
    (fun e he => (horigin {0} {0} h₀ h₀ e he).2)
    (fun I J hI hJ => (hQTests I J (chartIndex_mem hI) (chartIndex_mem hJ)).1) hoff b hb
  obtain ⟨t, ht, htCech, ht0⟩ := exists_graphOriginCocycle h j₂ hqp b
  have huG := (T).restrict_joint_left_mem_cycles (n := nG) (z := zG) hu
  have huT := (T).restrict_joint_right_mem_cycles (n := nG) (z := zG) hu
  have hboundary := (T).chartPart_sub_mem_boundary_of_joint hT hG hu hg ht
    (fun I J hI hJ => (hGTests I J (chartIndex_mem hI) (chartIndex_mem hJ)).1)
    (fun I J hI hJ => (hOTests I J (chartIndex_mem hI) (chartIndex_mem hJ)).1)
  rw [← htCech]
  apply hboundary
  · intro i j
    let g₁ (K : Finset G) := g (uni (uni {i} {j}) K)
    let u₁ (K : Finset G) := u (uni (uni {i} {j}) (uni K ∅))
    have hg₁ := (T).singletonColumn_mem_cycles hg i j
    have hu₁ : u₁ ∈ ((T).columnComplex nG zG {i} {j}).Z (d : ℤ) := by
      simpa only [u₁, restrictKoszulIndices, lft_uni, rgt_uni, map_joinedLeft] using
        (T).singletonColumn_mem_cycles huG i j
    have hi := Finset.mem_singleton_self i
    have hj := Finset.mem_singleton_self j
    refine (hGTests {i} {j} hi hj).2 (g₁ - u₁) (sub_mem hg₁ hu₁) (fun e he => ?_)
    obtain ⟨hI, hJ, f, hf, hval⟩ := hgraph {i} {j} hi hj e he
    have hi₀ := Finset.mem_singleton.mp (hI ▸ hi)
    have hj₀ := Finset.mem_singleton.mp (hJ ▸ hj)
    subst i
    subst j
    let C := (B) {0} {0}
    let R := loc B₀ f.1
    let eps : k := (-1 : k) ^ d
    let rQ : Q → C := graphColumnWeights h j₂ (q := q) (p := p) h₀ h₀ hQ
    let c₀ : Finset Q → DR k L := fun K => u (uni (uni {0} {0}) K)
    let c := ((T).scaleColumn nQ 0 0).symm c₀
    have hR : loc C e = R := loc_eq_of_val_iff C e hval
    let r (l : Q) : R := ⟨rQ l, hR ▸ le_loc C e (rQ l).property⟩
    have hc₀ := (T).singletonColumn_mem_cycles hu 0 0
    have hc := (graphColumn_scale_mem_cycles_iff h j₂ hqp h₀ h₀ hQ d c).mp
      ((((T).scaleColumn nQ 0 0).apply_symm_apply c₀).symm ▸ hc₀)
    have hcR := chartKoszul_cycles_le_localCycles C d rQ e d hc
    rw [hR] at hcR
    have hrg (l : G) : (r (eG l) : L) =
        graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) l :=
      congrArg (fun x : C => (x : L)) (graphColumnWeights_joint_left h j₂ h₀ h₀ hG l)
    have hro (l : Fin d) : r (eO l) = localOriginCoordinate f l := by
      apply Subtype.ext
      exact (congrArg (fun x : C => (x : L))
        (graphColumnWeights_joint_right h j₂ h₀ h₀ hG l)).trans
        (graphColumnWeights_leftOrigin h j₂ (q := q) (p := p) h₀ h₀ l)
    obtain ⟨s, hs, hsVal⟩ := hvalue f hf
    obtain ⟨hsmem, hsEval⟩ := (val_iff_loc B₀ f.1 s _).mp hsVal
    let a : R := algebraMap k R eps * Subalgebra.inclusion (le_loc B₀ f.1) b
    let s' : R := algebraMap k R eps * ⟨s, hsmem⟩
    have hsg (v : R) : ((algebraMap k R eps * v : R) : L) • originAffineVolume k L x =
        eps • ((v : L) • originAffineVolume k L x) := by
      change (algebraMap k L eps * (v : L)) • originAffineVolume k L x = _
      rw [mul_smul, IsScalarTower.algebraMap_smul L]
    have ha : c sO = (a : L) • originAffineVolume k L x :=
      huO.trans (hsg (Subalgebra.inclusion (le_loc B₀ f.1) b)).symm
    have hse : locEval B₀ f.1 s' = (1 - A f).det * locEval B₀ f.1 a := by
      simp only [s', a, map_mul, hsEval, locEval_inclusion]
      ac_rfl
    have hcomp := sub_mem_selectedGraphBoundary_of_residue h j₂ hL f hz hf (A f) (hrow f hf)
      (hdet f hf) r hrg hro hcR a s' ha hse
    have huns := (T).unscale_restrictKoszulIndices eG (n := nQ) 0 0 c₀ sG
    have hn : (nQ) ∘ eG = (nG) := rfl
    rw [hSG, hn] at huns
    have huc : ((T).scaleColumn nG 0 0).symm u₁ sG = c sQ := by
      simpa only [c, c₀, u₁, eG, map_joinedLeft] using huns
    have hsc : ((T).scaleColumn nG 0 0).symm g₁ sG = (s' : L) • originAffineVolume k L x :=
      hs.trans (hsg (⟨s, hsmem⟩ : R)).symm
    change ((T).scaleColumn nG 0 0).symm (g₁ - u₁) sG ∈ _
    rw [map_sub, Pi.sub_apply, hsc, huc, hR]
    exact hcomp
  · intro i j
    let u₁ (K : Finset (Fin d)) := u (uni (uni {i} {j}) (uni ∅ K))
    let t₁ (K : Finset (Fin d)) := t (uni (uni {i} {j}) K)
    have ht₁ := (T).singletonColumn_mem_cycles ht i j
    have hu₁ : u₁ ∈ ((T).columnComplex nT (T).leftOriginWeights {i} {j}).Z (d : ℤ) := by
      simpa only [u₁, restrictKoszulIndices, lft_uni, rgt_uni, map_joinedRight] using
        (T).singletonColumn_mem_cycles huT i j
    have hi := Finset.mem_singleton_self i
    have hj := Finset.mem_singleton_self j
    refine (hOTests {i} {j} hi hj).2 (u₁ - t₁) (sub_mem hu₁ ht₁) (fun e he => ?_)
    obtain ⟨hI, f, hval⟩ := horigin {i} {j} hi hj e he
    have hi₀ := Finset.mem_singleton.mp (hI ▸ hi)
    subst i
    have hU : selectedIndices (OrderEmbedding.id (Fin d)) = Finset.univ := by
      simp [selectedIndices, OrderEmbedding.id]
    rw [hU, map_sub, Pi.sub_apply, show ((T).scaleColumn nT 0 j).symm t₁ Finset.univ = _ from ht0 j]
    by_cases hj₀ : j = 0
    · subst j
      have huns := (T).unscale_restrictKoszulIndices eO (n := nQ) 0 0
        (fun K => u (uni (uni {0} {0}) K)) Finset.univ
      have hn : (nQ) ∘ eO = (nT) := rfl
      rw [hSO, hn] at huns
      have heq : ((T).scaleColumn nT 0 0).symm u₁ Finset.univ =
          (-1 : k) ^ d • ((b : L) • originAffineVolume k L x) :=
        (by simpa only [u₁, eO, map_joinedRight] using huns.trans huO)
      rw [heq, sub_self]
      exact zero_mem _
    · have heq : ((T).scaleColumn nT 0 j).symm u₁ Finset.univ = 0 := by
        have he0 := huOff 0 j (uni (∅ : Finset G) Finset.univ) (Or.inr hj₀)
          (by simp only [card_uni, Finset.card_empty, Finset.card_univ, Fintype.card_fin, zero_add])
        change (T).act (((T).normalizationProduct nT 0 j Finset.univ)⁻¹ : Lˣ)
          (u (uni (uni {0} {j}) (uni ∅ Finset.univ))) = 0
        rw [he0, map_zero]
      have hf : ¬ (Fixed) f := by
        intro hf
        exact hj₀ (Finset.mem_singleton.mp
          (rightChart_subset_origin_of_fixed_localValues h j₂ e f hval hf hj))
      let R := loc B₀ f.1
      let eps : k := (-1 : k) ^ d
      let a : R := -(algebraMap k R eps * Subalgebra.inclusion (le_loc B₀ f.1) b)
      have ha : locEval B₀ f.1 a = 0 := by
        simp only [a, map_neg, map_mul, locEval_inclusion, hb f hf, mul_zero, neg_zero]
      have hf' : (a : L) • originAffineVolume k L x =
          0 - (-1 : k) ^ d • ((b : L) • originAffineVolume k L x) := by
        change (-(algebraMap k L eps * (b : L))) • originAffineVolume k L x = _
        rw [neg_smul, mul_smul, IsScalarTower.algebraMap_smul L, zero_sub]
      let e₀ := OrderEmbedding.id (Fin d)
      have hspan : Ideal.span (Set.range fun j => localOriginCoordinate f (e₀ j)) =
          RingHom.ker (locEval B₀ f.1).toRingHom := hL.span_localOriginCoordinates f
      have hB := (hL.mem_selectedBoundaryValues_iff_residue f
        (localOriginCoordinate f) e₀ hspan a).mpr ha
      have hLoc := loc_eq_of_val_iff ((B) {0} {j}) e hval
      rw [heq, ← hf', hLoc]
      have hw :
          (fun l => Algebra.lsmul k k (DR k L) (localOriginCoordinate f l : L)) =
          fun l => Algebra.lsmul k k (DR k L)
            (graphColumnWeights h j₂ (q := q) (p := p) h₀ hj hO l : L) :=
        funext fun l => congrArg (Algebra.lsmul k k (DR k L))
          (graphColumnWeights_leftOrigin h j₂ (q := q) (p := p) h₀ hj l).symm
      exact hw ▸ hB

end GlobalTheory.WH
