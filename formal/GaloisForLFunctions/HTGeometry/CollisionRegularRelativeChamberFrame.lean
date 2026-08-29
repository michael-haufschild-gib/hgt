import GaloisForLFunctions.HTGeometry.ScalarCDDIntertwinerInvariance
import GaloisForLFunctions.HTGeometry.IncubationTubeTransport

open Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section HyperplaneGlue

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]

/-- Equal-constant Lipschitz gluing across one linear wall inside a convex carrier. -/
theorem Convex.lipschitzOnWith_of_linear_halfspaces
    {s : Set E} (hs : Convex ℝ s) {K : NNReal} {f : E → F} (ell : E →L[ℝ] ℝ)
    (hneg : LipschitzOnWith K f (s ∩ {x | ell x ≤ 0}))
    (hpos : LipschitzOnWith K f (s ∩ {x | 0 ≤ ell x})) :
    LipschitzOnWith K f s := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hneg hpos ⊢
  have cross : ∀ x ∈ s, ∀ y ∈ s, ell x ≤ 0 → 0 ≤ ell y →
      dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
    intro x hx y hy hxneg hypos
    by_cases hden : ell y - ell x = 0
    · have hx0 : ell x = 0 := by linarith
      have hy0 : ell y = 0 := by linarith
      apply hneg x ⟨hx, hxneg⟩ y
      exact ⟨hy, hy0.le⟩
    · have hdenpos : 0 < ell y - ell x := lt_of_le_of_ne (sub_nonneg.mpr (hxneg.trans hypos))
          (Ne.symm hden)
      let t : ℝ := -ell x / (ell y - ell x)
      have ht0 : 0 ≤ t := div_nonneg (neg_nonneg.mpr hxneg) hdenpos.le
      have ht1 : t ≤ 1 := (div_le_one hdenpos).2 (by linarith)
      let c : E := (AffineMap.lineMap x y) t
      have hc : c ∈ s := hs.lineMap_mem hx hy ⟨ht0, ht1⟩
      have hellc : ell c = 0 := by
        simp only [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          map_add, map_smul, map_sub]
        dsimp [t]
        field_simp
        ring
      have hdistLeft : dist x c = t * dist x y := by
        change dist x ((AffineMap.lineMap x y) t) = _
        rw [dist_comm, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht0]
      have hdistRight : dist c y = (1 - t) * dist x y := by
        change dist ((AffineMap.lineMap x y) t) y = _
        rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)]
      calc
        dist (f x) (f y) ≤ dist (f x) (f c) + dist (f c) (f y) := dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist x c + (K : ℝ) * dist c y :=
          add_le_add (hneg x ⟨hx, hxneg⟩ c ⟨hc, by change ell c ≤ 0; rw [hellc]⟩)
            (hpos c ⟨hc, by change 0 ≤ ell c; rw [hellc]⟩ y ⟨hy, hypos⟩)
        _ = (K : ℝ) * dist x y := by rw [hdistLeft, hdistRight]; ring
  intro x hx y hy
  rcases le_total (ell x) 0 with hxneg | hxpos
  · rcases le_total (ell y) 0 with hyneg | hypos
    · exact hneg x ⟨hx, hxneg⟩ y ⟨hy, hyneg⟩
    · exact cross x hx y hy hxneg hypos
  · rcases le_total (ell y) 0 with hyneg | hypos
    · rw [dist_comm, dist_comm x y]
      exact cross y hy x hx hyneg hxpos
    · exact hpos x ⟨hx, hxpos⟩ y ⟨hy, hypos⟩

end HyperplaneGlue

section Arrangement

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]

/-- Closed sign cell of a finite central hyperplane arrangement. Both signs contain the wall. -/
def hyperplaneCell {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ)) (sign : Fin m → Bool) : Set E :=
  {x | ∀ r, if sign r then ell r x ≤ 0 else 0 ≤ ell r x}

theorem convex_hyperplaneCell {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ))
    (sign : Fin m → Bool) : Convex ℝ (hyperplaneCell ell sign) := by
  rw [show hyperplaneCell ell sign = ⋂ r : Fin m,
      if sign r then {x | ell r x ≤ 0} else {x | 0 ≤ ell r x} by
    ext x
    simp only [hyperplaneCell, mem_setOf_eq, mem_iInter]
    constructor <;> intro h r
    · have hr := h r
      cases hsign : sign r <;> simp [hsign] at hr ⊢ <;> exact hr
    · have hr := h r
      cases hsign : sign r <;> simp [hsign] at hr ⊢ <;> exact hr]
  apply convex_iInter
  intro r
  split
  · exact convex_halfSpace_le (ell r).toLinearMap.isLinear 0
  · exact convex_halfSpace_ge (ell r).toLinearMap.isLinear 0

/-- A common Lipschitz constant on every closed cell of a finite linear arrangement is the same
global Lipschitz constant. Repeated wall gluing incurs no factor depending on cell count. -/
theorem Convex.lipschitzOnWith_of_hyperplaneCells
    {s : Set E} (hs : Convex ℝ s) {K : NNReal} {f : E → F}
    {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ))
    (hlocal : ∀ sign : Fin m → Bool,
      LipschitzOnWith K f (s ∩ hyperplaneCell ell sign)) :
    LipschitzOnWith K f s := by
  induction m generalizing s with
  | zero =>
      simpa [hyperplaneCell] using hlocal (fun r => Fin.elim0 r)
  | succ m ih =>
      let ellTail : Fin m → (E →L[ℝ] ℝ) := fun r => ell r.succ
      let sneg : Set E := s ∩ {x | ell 0 x ≤ 0}
      let spos : Set E := s ∩ {x | 0 ≤ ell 0 x}
      have hsneg : Convex ℝ sneg :=
        hs.inter (convex_halfSpace_le (ell 0).toLinearMap.isLinear 0)
      have hspos : Convex ℝ spos :=
        hs.inter (convex_halfSpace_ge (ell 0).toLinearMap.isLinear 0)
      have hneg : LipschitzOnWith K f sneg := by
        apply ih hsneg ellTail
        intro sign
        have hset : sneg ∩ hyperplaneCell ellTail sign =
            s ∩ hyperplaneCell ell (Fin.cons true sign) := by
          ext x
          simp [sneg, hyperplaneCell, ellTail, Fin.forall_fin_succ, and_assoc]
        rw [hset]
        exact hlocal (Fin.cons true sign)
      have hpos : LipschitzOnWith K f spos := by
        apply ih hspos ellTail
        intro sign
        have hset : spos ∩ hyperplaneCell ellTail sign =
            s ∩ hyperplaneCell ell (Fin.cons false sign) := by
          ext x
          simp [spos, hyperplaneCell, ellTail, Fin.forall_fin_succ, and_assoc]
        rw [hset]
        exact hlocal (Fin.cons false sign)
      exact Convex.lipschitzOnWith_of_linear_halfspaces hs (ell 0) hneg hpos

/-- Global form of finite-arrangement Lipschitz gluing. -/
theorem lipschitzWith_of_hyperplaneCells
    {K : NNReal} {f : E → F} {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ))
    (hlocal : ∀ sign : Fin m → Bool, LipschitzOnWith K f (hyperplaneCell ell sign)) :
    LipschitzWith K f := by
  rw [← lipschitzOnWith_univ]
  apply Convex.lipschitzOnWith_of_hyperplaneCells convex_univ ell
  simpa using hlocal

/-- Canonical closed-cell sign choice; equality is assigned to the nonpositive side. -/
def canonicalHyperplaneSign {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ)) (x : E) : Fin m → Bool :=
  fun r => decide (ell r x ≤ 0)

theorem mem_hyperplaneCell_canonicalSign {m : ℕ}
    (ell : Fin m → (E →L[ℝ] ℝ)) (x : E) :
    x ∈ hyperplaneCell ell (canonicalHyperplaneSign ell x) := by
  intro r
  simp only [canonicalHyperplaneSign]
  by_cases h : ell r x ≤ 0
  · simp [h]
  · simp [h, le_of_not_ge h]

/-- Global frame obtained by the canonical chamber choice. -/
def gluedHyperplaneFrame {m : ℕ} (ell : Fin m → (E →L[ℝ] ℝ))
    (piece : (Fin m → Bool) → E → F) (x : E) : F :=
  piece (canonicalHyperplaneSign ell x) x

omit [PseudoMetricSpace F] in
/-- Collision-overlap agreement makes the canonical glued value equal every chamber formula
whose closed chamber contains the point. -/
theorem gluedHyperplaneFrame_eq_piece {m : ℕ} {ell : Fin m → (E →L[ℝ] ℝ)}
    {piece : (Fin m → Bool) → E → F}
    (hoverlap : ∀ sign tau x, x ∈ hyperplaneCell ell sign →
      x ∈ hyperplaneCell ell tau → piece sign x = piece tau x)
    (sign : Fin m → Bool) {x : E} (hx : x ∈ hyperplaneCell ell sign) :
    gluedHyperplaneFrame ell piece x = piece sign x := by
  exact hoverlap _ _ x (mem_hyperplaneCell_canonicalSign ell x) hx

/-- Closed-chamber overlap agreement plus one common chamberwise Lipschitz constant yields a
globally Lipschitz glued frame with exactly the same constant. -/
theorem gluedHyperplaneFrame_lipschitzWith {m : ℕ}
    (ell : Fin m → (E →L[ℝ] ℝ)) (piece : (Fin m → Bool) → E → F) {K : NNReal}
    (hoverlap : ∀ sign tau x, x ∈ hyperplaneCell ell sign →
      x ∈ hyperplaneCell ell tau → piece sign x = piece tau x)
    (hpiece : ∀ sign, LipschitzOnWith K (piece sign) (hyperplaneCell ell sign)) :
    LipschitzWith K (gluedHyperplaneFrame ell piece) := by
  apply lipschitzWith_of_hyperplaneCells ell
  intro sign
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [gluedHyperplaneFrame_eq_piece hoverlap sign hx,
    gluedHyperplaneFrame_eq_piece hoverlap sign hy]
  exact (lipschitzOnWith_iff_dist_le_mul.mp (hpiece sign)) x hx y hy

omit [PseudoMetricSpace F] in
/-- Any pointwise property of every closed-chamber trace survives collision gluing. -/
theorem gluedHyperplaneFrame_property {m : ℕ}
    (ell : Fin m → (E →L[ℝ] ℝ)) (piece : (Fin m → Bool) → E → F)
    (P : F → Prop)
    (hpiece : ∀ sign x, x ∈ hyperplaneCell ell sign → P (piece sign x)) (x : E) :
    P (gluedHyperplaneFrame ell piece x) :=
  hpiece _ x (mem_hyperplaneCell_canonicalSign ell x)

end Arrangement

section RelativeFrame

variable {A : Type*} [Monoid A]

/-- Relative chamber frame `target * source⁻¹`, with inverse supplied explicitly. -/
def relativeChamberFrame (target sourceInv : A) : A := target * sourceInv

/-- Stabilizer cancellation in the right-action convention. If source and target traces acquire
the same right collision factor, their relative chamber frames agree exactly. -/
theorem relativeChamberFrame_eq_of_right_collisionFactor
    {targetPi sourceInvPi targetTau sourceInvTau collision collisionInv : A}
    (hcollision : collision * collisionInv = 1)
    (htarget : targetTau = targetPi * collision)
    (hsourceInv : sourceInvTau = collisionInv * sourceInvPi) :
    relativeChamberFrame targetTau sourceInvTau =
      relativeChamberFrame targetPi sourceInvPi := by
  rw [relativeChamberFrame, relativeChamberFrame, htarget, hsourceInv]
  rw [mul_assoc targetPi collision, ← mul_assoc collision collisionInv,
    hcollision, one_mul]

end RelativeFrame

section RelativeFrameNorm

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Product of two exactly unitary chamber cocycles is an exactly unitary relative frame. This
uses only explicit two-sided inverse and contractivity, so it applies to operator-valued frames. -/
theorem relativeChamberFrame_twoSidedInverse_norm_eq_one
    (target targetInv source sourceInv : A)
    (htargetRight : target * targetInv = 1) (htargetLeft : targetInv * target = 1)
    (hsourceRight : source * sourceInv = 1) (hsourceLeft : sourceInv * source = 1)
    (htargetNorm : ‖target‖ ≤ 1) (htargetInvNorm : ‖targetInv‖ ≤ 1)
    (hsourceNorm : ‖source‖ ≤ 1) (hsourceInvNorm : ‖sourceInv‖ ≤ 1) :
    relativeChamberFrame target sourceInv * relativeChamberFrame source targetInv = 1 ∧
      relativeChamberFrame source targetInv * relativeChamberFrame target sourceInv = 1 ∧
      ‖relativeChamberFrame target sourceInv‖ = 1 ∧
      ‖relativeChamberFrame source targetInv‖ = 1 := by
  have hright : relativeChamberFrame target sourceInv *
      relativeChamberFrame source targetInv = 1 := by
    simp only [relativeChamberFrame]
    calc
      (target * sourceInv) * (source * targetInv) =
          target * (sourceInv * source) * targetInv := by noncomm_ring
      _ = target * 1 * targetInv := by rw [hsourceLeft]
      _ = 1 := by simpa using htargetRight
  have hleft : relativeChamberFrame source targetInv *
      relativeChamberFrame target sourceInv = 1 := by
    simp only [relativeChamberFrame]
    calc
      (source * targetInv) * (target * sourceInv) =
          source * (targetInv * target) * sourceInv := by noncomm_ring
      _ = source * 1 * sourceInv := by rw [htargetLeft]
      _ = 1 := by simpa using hsourceRight
  have hforwardNorm : ‖relativeChamberFrame target sourceInv‖ ≤ 1 := by
    calc
      ‖relativeChamberFrame target sourceInv‖ ≤ ‖target‖ * ‖sourceInv‖ :=
        by exact norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul htargetNorm hsourceInvNorm (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hinverseNorm : ‖relativeChamberFrame source targetInv‖ ≤ 1 := by
    calc
      ‖relativeChamberFrame source targetInv‖ ≤ ‖source‖ * ‖targetInv‖ :=
        by exact norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hsourceNorm htargetInvNorm (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨hforwardEq, hinverseEq⟩ := norm_eq_one_of_twoSidedInverse_of_norm_le_one
    _ _ hright hleft hforwardNorm hinverseNorm
  exact ⟨hright, hleft, hforwardEq, hinverseEq⟩

end RelativeFrameNorm

section OrderedDerivative

variable {I A : Type*} [NormedRing A] [NormOneClass A]

/-- Leibniz expansion of the directional derivative of a noncommutative ordered word. -/
def orderedWordDerivative : List I → (I → A) → (I → A) → A
  | [], _, _ => 0
  | r :: word, F, dF =>
      dF r * orderedWordProduct word F + F r * orderedWordDerivative word F dF

/-- Unitary undifferentiated factors make the derivative of a word cost only the sum of the
differentiated-factor norms. -/
theorem norm_orderedWordDerivative_le_sum (word : List I) (F dF : I → A)
    (hF : ∀ r ∈ word, ‖F r‖ ≤ 1) :
    ‖orderedWordDerivative word F dF‖ ≤ (word.map fun r => ‖dF r‖).sum := by
  induction word with
  | nil => simp [orderedWordDerivative]
  | cons r word ih =>
      have hr : ‖F r‖ ≤ 1 := hF r (by simp)
      have htail : ∀ s ∈ word, ‖F s‖ ≤ 1 := by
        intro s hs
        exact hF s (List.mem_cons_of_mem r hs)
      have hi := ih htail
      have hprod : ‖orderedWordProduct word F‖ ≤ 1 := by
        have h := norm_orderedWordProduct_le_rpow_sum word F (M := 1) (by norm_num)
          (fun _ => 0) (by intro s hs; simpa using htail s hs)
        simpa using h
      calc
        ‖orderedWordDerivative (r :: word) F dF‖ ≤
            ‖dF r * orderedWordProduct word F‖ +
              ‖F r * orderedWordDerivative word F dF‖ := by
                simpa [orderedWordDerivative] using
                  norm_add_le (dF r * orderedWordProduct word F)
                    (F r * orderedWordDerivative word F dF)
        _ ≤ ‖dF r‖ * ‖orderedWordProduct word F‖ +
              ‖F r‖ * ‖orderedWordDerivative word F dF‖ :=
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖dF r‖ * 1 + 1 * (word.map fun s => ‖dF s‖).sum :=
          add_le_add
            (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
            (mul_le_mul hr hi (norm_nonneg _) zero_le_one)
        _ = ((r :: word).map fun s => ‖dF s‖).sum := by simp

/-- Equation `(5)`, first inequality: if the derivative of factor `r` costs
`L |h_i-h_j|`, the whole noncommutative unitary word costs `L` times the pair-difference sum. -/
theorem norm_orderedWordDerivative_le_pairBudget
    (word : List I) (F dF : I → A) (delta : I → ℝ) {L : ℝ}
    (hF : ∀ r ∈ word, ‖F r‖ ≤ 1)
    (hdF : ∀ r ∈ word, ‖dF r‖ ≤ L * |delta r|) :
    ‖orderedWordDerivative word F dF‖ ≤ L * (word.map fun r => |delta r|).sum := by
  refine (norm_orderedWordDerivative_le_sum word F dF hF).trans ?_
  calc
    (word.map fun r => ‖dF r‖).sum ≤ (word.map fun r => L * |delta r|).sum := by
      apply List.sum_le_sum
      intro k hk
      exact hdF k hk
    _ = L * (word.map fun r => |delta r|).sum :=
      List.sum_map_mul_left word (fun r => |delta r|) L

end OrderedDerivative

section PairDifferenceEnergy

/-- Sum of squared coordinate differences over strict unordered pairs, in recursive pair order. -/
def pairDifferenceEnergy : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, h => pairDifferenceEnergy (Fin.init h) +
      ∑ i : Fin n, (h i.castSucc - h (Fin.last n)) ^ 2

/-- Exact variance identity for the strict pair-difference energy. -/
theorem pairDifferenceEnergy_eq (n : ℕ) (h : Fin n → ℝ) :
    pairDifferenceEnergy h =
      n * (∑ i, h i ^ 2) - (∑ i, h i) ^ 2 := by
  induction n with
  | zero => simp [pairDifferenceEnergy]
  | succ n ih =>
      let a : ℝ := h (Fin.last n)
      let q : Fin n → ℝ := Fin.init h
      have hcross : (∑ i : Fin n, (h i.castSucc - h (Fin.last n)) ^ 2) =
          (∑ i : Fin n, q i ^ 2) - 2 * a * (∑ i : Fin n, q i) + n * a ^ 2 := by
        calc
          (∑ i : Fin n, (h i.castSucc - h (Fin.last n)) ^ 2) =
              ∑ i : Fin n, (q i ^ 2 - 2 * a * q i + a ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                simp only [q, Fin.init_def, a]
                ring
          _ = (∑ i : Fin n, q i ^ 2) - 2 * a * (∑ i : Fin n, q i) + n * a ^ 2 := by
                simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                rw [Finset.mul_sum]
                simp
      rw [pairDifferenceEnergy, ih, hcross]
      have hsum : (∑ i : Fin (n + 1), h i) = (∑ i : Fin n, q i) + a := by
        rw [Fin.sum_univ_castSucc]
        simp [q, a, Fin.init_def]
      have hsumsq : (∑ i : Fin (n + 1), h i ^ 2) =
          (∑ i : Fin n, q i ^ 2) + a ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        simp [q, a, Fin.init_def]
      rw [hsum, hsumsq]
      push_cast
      ring

/-- Card identity `(5)`: strict pairwise squared differences are bounded by `n` times squared
Euclidean coordinate norm. -/
theorem pairDifferenceEnergy_le (n : ℕ) (h : Fin n → ℝ) :
    pairDifferenceEnergy h ≤ n * ∑ i, h i ^ 2 := by
  rw [pairDifferenceEnergy_eq]
  nlinarith [sq_nonneg (∑ i, h i)]

/-- Recursive list of strict coordinate differences, with one entry per unordered pair. -/
def pairDifferences : {n : ℕ} → (Fin n → ℝ) → List ℝ
  | 0, _ => []
  | n + 1, h => pairDifferences (Fin.init h) ++
      List.ofFn (fun i : Fin n => h i.castSucc - h (Fin.last n))

@[simp]
theorem pairDifferences_length (n : ℕ) (h : Fin n → ℝ) :
    (pairDifferences h).length = n.choose 2 := by
  induction n with
  | zero => simp [pairDifferences]
  | succ n ih =>
      rw [pairDifferences, List.length_append, ih, List.length_ofFn, Nat.choose]
      simp [Nat.choose_one_right, add_comm]

theorem pairDifferences_sum_sq (n : ℕ) (h : Fin n → ℝ) :
    ((pairDifferences h).map fun x => x ^ 2).sum = pairDifferenceEnergy h := by
  induction n with
  | zero => simp [pairDifferences, pairDifferenceEnergy]
  | succ n ih =>
      rw [pairDifferences, pairDifferenceEnergy, List.map_append, List.sum_append, ih]
      rw [List.map_ofFn, List.sum_ofFn]
      rfl

/-- Cauchy--Schwarz and the variance identity give the sharp chamber directional budget
`sum_{i<j}|h_i-h_j| ≤ sqrt(C(n,2) n) · ||h||₂`. -/
theorem sum_abs_pairDifferences_sq_le (n : ℕ) (h : Fin n → ℝ) :
    ((pairDifferences h).map abs).sum ^ 2 ≤
      (n.choose 2 : ℝ) * n * ∑ i, h i ^ 2 := by
  let c : Fin (pairDifferences h).length → ℝ := fun i => (pairDifferences h).get i
  have hcs := sq_sum_abs_le_card_mul_sum_sq c
  have habs : (∑ i, |c i|) = ((pairDifferences h).map abs).sum := by
    calc
      (∑ i, |c i|) = (List.ofFn (fun i => |c i|)).sum := List.sum_ofFn.symm
      _ = ((List.ofFn c).map abs).sum := by rw [List.map_ofFn]; rfl
      _ = ((pairDifferences h).map abs).sum := by
        change ((List.ofFn (pairDifferences h).get).map abs).sum = _
        rw [List.ofFn_get]
  have hsq : (∑ i, c i ^ 2) = pairDifferenceEnergy h := by
    calc
      (∑ i, c i ^ 2) = (List.ofFn (fun i => c i ^ 2)).sum := List.sum_ofFn.symm
      _ = ((List.ofFn c).map fun x => x ^ 2).sum := by rw [List.map_ofFn]; rfl
      _ = ((pairDifferences h).map fun x => x ^ 2).sum := by
        change ((List.ofFn (pairDifferences h).get).map fun x => x ^ 2).sum = _
        rw [List.ofFn_get]
      _ = pairDifferenceEnergy h := pairDifferences_sum_sq n h
  rw [habs, hsq, Fintype.card_fin, pairDifferences_length] at hcs
  exact hcs.trans (by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left (pairDifferenceEnergy_le n h)
      (Nat.cast_nonneg (n.choose 2)))

private theorem two_mul_choose_two_eq_mul_pred_chamber (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  refine Nat.mul_div_cancel' ?_
  rcases n with _ | m
  · simp
  · rw [Nat.succ_sub_one]
    have h := (Nat.even_mul_succ_self m).two_dvd
    rwa [mul_comm] at h

theorem sum_abs_pairDifferences_le (n : ℕ) (h : Fin n → ℝ) :
    ((pairDifferences h).map abs).sum ≤
      n * Real.sqrt ((n - 1 : ℕ) / 2) * Real.sqrt (∑ i, h i ^ 2) := by
  have hsq := sum_abs_pairDifferences_sq_le n h
  have hsumNonneg : 0 ≤ ((pairDifferences h).map abs).sum := by
    exact List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg y
  have hcoordNonneg : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcardNonneg : 0 ≤ (n.choose 2 : ℝ) * n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hsumNonneg, Real.sqrt_mul hcardNonneg] at hsqrt
  have hchoose : (2 : ℝ) * n.choose 2 = (n : ℝ) * (n - 1 : ℕ) := by
    exact_mod_cast two_mul_choose_two_eq_mul_pred_chamber n
  have hhalfNonneg : 0 ≤ ((n - 1 : ℕ) : ℝ) / 2 := by positivity
  have hsqrtSq : Real.sqrt (((n - 1 : ℕ) : ℝ) / 2) ^ 2 =
      ((n - 1 : ℕ) : ℝ) / 2 := Real.sq_sqrt hhalfNonneg
  have hroot : Real.sqrt ((n.choose 2 : ℝ) * n) =
      n * Real.sqrt ((n - 1 : ℕ) / 2) := by
    rw [← Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))]
    congr 1
    rw [mul_pow, hsqrtSq]
    have hscaled := congrArg (fun x : ℝ => x * (n : ℝ) / 2) hchoose
    ring_nf at hscaled ⊢
    exact hscaled
  rw [hroot] at hsqrt
  exact hsqrt

end PairDifferenceEnergy

section WallSeam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two chamber traces glued continuously at a wall: constant on the nonpositive side and `A` on
the positive side. -/
def wallFrame (base : E) (A : ℝ → E) (u : ℝ) : E :=
  if u ≤ 0 then base else A u

/-- Exact wall seam: if the positive chamber has nonzero normal derivative while the negative
chamber is constant, the continuously glued frame is not differentiable at the wall. -/
theorem wallFrame_not_differentiableAt
    {base : E} {A : ℝ → E} {v : E} (hA0 : A 0 = base)
    (hA : HasDerivAt A v 0) (hv : v ≠ 0) :
    ¬ DifferentiableAt ℝ (wallFrame base A) 0 := by
  intro hdiff
  have hc : HasDerivAt (wallFrame base A) (deriv (wallFrame base A) 0) 0 :=
    hdiff.hasDerivAt
  have hcslope := hasDerivAt_iff_tendsto_slope.mp hc
  have hpos : Tendsto (slope (wallFrame base A) 0) (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (deriv (wallFrame base A) 0)) :=
    hcslope.mono_left
      (nhdsWithin_mono _ fun x hx => mem_compl_singleton_iff.mpr (ne_of_gt hx))
  have hneg : Tendsto (slope (wallFrame base A) 0) (nhdsWithin (0 : ℝ) (Iio 0))
      (nhds (deriv (wallFrame base A) 0)) :=
    hcslope.mono_left
      (nhdsWithin_mono _ fun x hx => mem_compl_singleton_iff.mpr (ne_of_lt hx))
  have hAslope := hasDerivAt_iff_tendsto_slope.mp hA
  have hApos : Tendsto (slope A 0) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds v) :=
    hAslope.mono_left
      (nhdsWithin_mono _ fun x hx => mem_compl_singleton_iff.mpr (ne_of_gt hx))
  have heqPos : slope (wallFrame base A) 0 =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)] slope A 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    simp [slope, wallFrame, not_le.mpr hxpos, hA0]
  have hposV : Tendsto (slope (wallFrame base A) 0) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds v) :=
    hApos.congr' heqPos.symm
  have hnegZero : Tendsto (slope (wallFrame base A) 0) (nhdsWithin (0 : ℝ) (Iio 0)) (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxneg : x < 0 := hx
    simp [slope, wallFrame, hxneg.le]
  have hderivV : deriv (wallFrame base A) 0 = v := tendsto_nhds_unique hpos hposV
  have hderivZero : deriv (wallFrame base A) 0 = 0 := tendsto_nhds_unique hneg hnegZero
  exact hv (hderivV.symm.trans hderivZero)

end WallSeam

section CollisionCapstone

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormOneClass A] [NormedSpace ℝ A]

/-- Exact common chamber Lipschitz constant from equation `(6)`. -/
def collisionFrameLipschitzConstant (L : ℝ) (n : ℕ) : NNReal :=
  Real.toNNReal (L * n * Real.sqrt ((n - 1 : ℕ) / 2))

theorem coe_collisionFrameLipschitzConstant {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    (collisionFrameLipschitzConstant L n : ℝ) =
      L * n * Real.sqrt ((n - 1 : ℕ) / 2) := by
  rw [collisionFrameLipschitzConstant, Real.coe_toNNReal]
  positivity

omit [NormOneClass A] in
/-- A chamberwise Fréchet derivative bound with the exact constant `(6)` produces the local
Lipschitz hypothesis used by the collision gluing theorem. -/
theorem collisionChamber_lipschitzOnWith_of_fderiv
    {n : ℕ} {L : ℝ} {s : Set E} (hs : Convex ℝ s) {f : E → A}
    {f' : E → E →L[ℝ] A}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hbound : ∀ x ∈ s, ‖f' x‖₊ ≤ collisionFrameLipschitzConstant L n) :
    LipschitzOnWith (collisionFrameLipschitzConstant L n) f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hf hbound hs

omit [NormedSpace ℝ A] in
/-- Card-level collision gluing theorem. Closed chamber traces that agree on every collision
overlap, are contractive two-sided inverses, and share the derivative-produced constant `(6)` glue
to globally continuous, globally Lipschitz, condition-number-one frames on the real locus. -/
theorem collisionRegular_relativeChamberFrame
    {n : ℕ} {L : ℝ}
    (ell : Fin (n.choose 2) → (E →L[ℝ] ℝ))
    (piece pieceInv : (Fin (n.choose 2) → Bool) → E → A)
    (hoverlap : ∀ sign tau x, x ∈ hyperplaneCell ell sign →
      x ∈ hyperplaneCell ell tau → piece sign x = piece tau x)
    (hoverlapInv : ∀ sign tau x, x ∈ hyperplaneCell ell sign →
      x ∈ hyperplaneCell ell tau → pieceInv sign x = pieceInv tau x)
    (hpiece : ∀ sign, LipschitzOnWith (collisionFrameLipschitzConstant L n)
      (piece sign) (hyperplaneCell ell sign))
    (hpieceInv : ∀ sign, LipschitzOnWith (collisionFrameLipschitzConstant L n)
      (pieceInv sign) (hyperplaneCell ell sign))
    (hright : ∀ sign x, x ∈ hyperplaneCell ell sign →
      piece sign x * pieceInv sign x = 1)
    (hleft : ∀ sign x, x ∈ hyperplaneCell ell sign →
      pieceInv sign x * piece sign x = 1)
    (hcontract : ∀ sign x, x ∈ hyperplaneCell ell sign → ‖piece sign x‖ ≤ 1)
    (hcontractInv : ∀ sign x, x ∈ hyperplaneCell ell sign → ‖pieceInv sign x‖ ≤ 1) :
    let frame := gluedHyperplaneFrame ell piece
    let frameInv := gluedHyperplaneFrame ell pieceInv
    LipschitzWith (collisionFrameLipschitzConstant L n) frame ∧
      LipschitzWith (collisionFrameLipschitzConstant L n) frameInv ∧
      Continuous frame ∧ Continuous frameInv ∧
      ∀ x, frame x * frameInv x = 1 ∧ frameInv x * frame x = 1 ∧
        ‖frame x‖ = 1 ∧ ‖frameInv x‖ = 1 := by
  dsimp only
  have hLip := gluedHyperplaneFrame_lipschitzWith ell piece hoverlap hpiece
  have hLipInv := gluedHyperplaneFrame_lipschitzWith ell pieceInv hoverlapInv hpieceInv
  refine ⟨hLip, hLipInv, hLip.continuous, hLipInv.continuous, ?_⟩
  intro x
  let sign := canonicalHyperplaneSign ell x
  have hx : x ∈ hyperplaneCell ell sign := mem_hyperplaneCell_canonicalSign ell x
  have hr : gluedHyperplaneFrame ell piece x * gluedHyperplaneFrame ell pieceInv x = 1 := by
    exact hright sign x hx
  have hl : gluedHyperplaneFrame ell pieceInv x * gluedHyperplaneFrame ell piece x = 1 := by
    exact hleft sign x hx
  have hn : ‖gluedHyperplaneFrame ell piece x‖ ≤ 1 := hcontract sign x hx
  have hnInv : ‖gluedHyperplaneFrame ell pieceInv x‖ ≤ 1 := hcontractInv sign x hx
  obtain ⟨hne, hnIne⟩ := norm_eq_one_of_twoSidedInverse_of_norm_le_one
    _ _ hr hl hn hnInv
  exact ⟨hr, hl, hne, hnIne⟩

end CollisionCapstone

end
end GaloisForLFunctions.HTGeometry
