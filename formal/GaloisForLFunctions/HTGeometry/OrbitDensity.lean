import GaloisForLFunctions.HTGeometry.OrbitSampleOpen
import GaloisForLFunctions.HTGeometry.EulerWindowEquiv
import GaloisForLFunctions.HTGeometry.WindowBox

/-!
# Density of the good sources

For a finite family of distinct jet monomials, the sources with a nonsingular evaluation matrix are
dense: sample points with distinct nodes are chosen first, from the open set they form together with
unrestricted jet values; substituting them into the determinant polynomial leaves a nonzero
polynomial in the jet values alone; a small ball around the jets of the *window-zeroed* source then
contains a jet value at which that polynomial does not vanish; and the free Euler jets of a
high-degree window realize the increment with coefficients inside the box.

Nothing below the prescribed degree is touched, so the produced source lies in every prescribed
basic neighbourhood of the given one.
-/

open MvPolynomial Metric

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### A uniform positive bound over a finite family -/

theorem exists_uniform_pos {m : ℕ} (f : Fin m → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ > 0, ∀ j, δ ≤ f j := by
  classical
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin m)) with h | h
  · refine ⟨1, one_pos, fun j => ?_⟩
    exact absurd (Finset.mem_univ j) (by rw [h]; simp)
  · refine ⟨Finset.univ.inf' h f, ?_, fun j => Finset.inf'_le f (Finset.mem_univ j)⟩
    show (0 : ℝ) < Finset.univ.inf' h f
    rw [Finset.lt_inf'_iff]
    exact fun j _ => hf j

/-! ### The specialized determinant polynomial -/

/-- The block values assembled from sample points and jet values. -/
def blockOf {n K : ℕ} (t : Fin K → ℂ) (Y : Fin K × (ι × Fin (n + 1)) → ℂ) :
    Fin K × Option (ι × Fin (n + 1)) → ℂ :=
  fun p => p.2.elim (t p.1) fun s => Y (p.1, s)

/-- The determinant polynomial with the sample points substituted. -/
def specDetPoly {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (t : Fin K → ℂ) :
    MvPolynomial (Fin K × (ι × Fin (n + 1))) ℂ :=
  MvPolynomial.bind₁
    (fun p : Fin K × Option (ι × Fin (n + 1)) =>
      p.2.elim (MvPolynomial.C (t p.1)) fun s => MvPolynomial.X (p.1, s))
    ((blockMonomialMatrix M).det)

omit [Fintype ι] [DecidableEq ι] in
theorem eval_specDetPoly {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (t : Fin K → ℂ)
    (Y : Fin K × (ι × Fin (n + 1)) → ℂ) :
    MvPolynomial.eval Y (specDetPoly M t) =
      Matrix.det (fun i a : Fin K => (M i).prod fun v e => (blockOf t Y (a, v)) ^ e) := by
  have hb : MvPolynomial.eval Y (specDetPoly M t) =
      MvPolynomial.eval
        (fun p : Fin K × Option (ι × Fin (n + 1)) => MvPolynomial.eval Y
          (p.2.elim (MvPolynomial.C (t p.1)) fun s => MvPolynomial.X (p.1, s)))
        ((blockMonomialMatrix M).det) :=
    eval₂Hom_bind₁ (RingHom.id ℂ) Y _ _
  have hfun : (fun p : Fin K × Option (ι × Fin (n + 1)) => MvPolynomial.eval Y
      (p.2.elim (MvPolynomial.C (t p.1)) fun s => MvPolynomial.X (p.1, s))) = blockOf t Y := by
    funext p
    obtain ⟨a, v⟩ := p
    cases v with
    | none => simp [blockOf]
    | some s => simp [blockOf]
  rw [hb, hfun, det_eval_blockMonomialMatrix]

/-! ### The fibers of the source map -/

/-- The members carried by one source. -/
abbrev srcFiber (src : ι → Fin L) (j : Fin L) : Type := {i : ι // src i = j}

/-- The nodes of one source at the sample points. -/
def fiberNode (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ} (t : Fin K → ℂ)
    (j : Fin L) : (srcFiber src j × Fin K) → ℂ :=
  fun p => orbNode lam src sh p.1.val (t p.2)

omit [Fintype ι] [DecidableEq ι] in
theorem fiberNode_ne_zero (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ}
    (t : Fin K → ℂ) (j : Fin L) (p : srcFiber src j × Fin K) : fiberNode lam src sh t j p ≠ 0 :=
  orbNode_ne_zero lam src sh _ _

omit [Fintype ι] in
theorem fiberNode_injective (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) {K : ℕ}
    {t : Fin K → ℂ} (hgood : GoodSamples lam src sh t) (j : Fin L) :
    Function.Injective (fiberNode lam src sh t j) := by
  intro p q hpq
  by_contra hne
  refine hgood (p.1.val, p.2) (q.1.val, q.2) (by rw [p.1.2, q.1.2]) ?_ hpq
  intro hEq
  refine hne ?_
  obtain ⟨hval, hsamp⟩ := Prod.mk.injEq .. ▸ hEq
  exact Prod.ext (Subtype.ext hval) hsamp

/-! ### The density theorem -/

/-- **Density of the good sources.**  For every finite family of distinct jet monomials and every
prescribed frozen prefix of the coefficients, some source family agreeing on that prefix has a
nonsingular evaluation matrix. -/
theorem exists_orbGood_agreeing
    (lam : Fin L → ℂ) (hlam : ∀ j, lam j ≠ 0) (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i'))
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (hM : Function.Injective M)
    (C₀ : Fin L → sourceBox) (N₀ : ℕ) :
    ∃ C : Fin L → sourceBox, (∀ (j : Fin L) (k : ℕ), k < N₀ → C j k = C₀ j k) ∧
      C ∈ orbGood lam src sh M := by
  classical
  obtain ⟨t0, hgood0⟩ := exists_goodSamples lam hlam src sh hdist K
  obtain ⟨V₀, hV₀U, hV₀det⟩ :=
    exists_blockValues_det_ne_zero (σ := Option (ι × Fin (n + 1))) hM
      (U := {V : (Fin K × Option (ι × Fin (n + 1))) → ℂ |
        GoodSamples lam src sh fun a => V (a, none)})
      (by
        have hc : Continuous fun V : (Fin K × Option (ι × Fin (n + 1))) → ℂ =>
            fun a => V (a, none) := continuous_pi fun a => continuous_apply (a, none)
        exact hc.isOpen_preimage _ (isOpen_goodSamples lam src sh K))
      ⟨fun p => p.2.elim (t0 p.1) fun _ => 0, hgood0⟩
  set t : Fin K → ℂ := fun a => V₀ (a, none) with ht
  have hgood : GoodSamples lam src sh t := hV₀U
  have hblock : blockOf t (fun q : Fin K × (ι × Fin (n + 1)) => V₀ (q.1, some q.2)) = V₀ := by
    funext p
    obtain ⟨a, v⟩ := p
    cases v with
    | none => rfl
    | some s => rfl
  have hP : specDetPoly M t ≠ 0 := by
    intro h
    refine hV₀det ?_
    have hev := eval_specDetPoly M t (fun q : Fin K × (ι × Fin (n + 1)) => V₀ (q.1, some q.2))
    rw [h, map_zero, hblock] at hev
    exact hev.symm
  set Wj : Fin L → ℕ := fun j => Fintype.card (srcFiber src j × Fin K) * (n + 1) with hWjdef
  set W : ℕ := Finset.univ.sup Wj with hWdef
  have hWjle : ∀ j, Wj j ≤ W := fun j => Finset.le_sup (Finset.mem_univ j)
  set Cz : Fin L → sourceBox := fun j => zeroWindowBox (C₀ j) N₀ W with hCzdef
  have hCzzero : ∀ (j : Fin L) (k : ℕ), N₀ ≤ k → k - N₀ < W → boxSeq (Cz j) k = 0 :=
    fun j k h1 h2 => boxSeq_zeroWindowBox_of_inside (C₀ j) N₀ W ⟨h1, h2⟩
  set Jz : Fin K × (ι × Fin (n + 1)) → ℂ :=
    fun q => famJetPoint (orbFun lam src sh Cz) n (t q.1) (some q.2) with hJzdef
  set ε : ℝ := (((N₀ + W).factorial : ℝ))⁻¹ with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    positivity
  have hnode0 : ∀ (j : Fin L) (p : srcFiber src j × Fin K), fiberNode lam src sh t j p ≠ 0 :=
    fun j p => fiberNode_ne_zero lam src sh t j p
  have hnodeinj : ∀ j : Fin L, Function.Injective (fiberNode lam src sh t j) :=
    fun j => fiberNode_injective lam src sh hgood j
  have hsmall : ∀ j : Fin L, ∃ δ > 0, ∀ J : (srcFiber src j × Fin K) → Fin (n + 1) → ℂ,
      (∀ a r, ‖J a r‖ < δ) →
      ∃ w : Fin (Wj j) → ℂ, (∀ i, ‖w i‖ < ε) ∧
        ∀ (a : srcFiber src j × Fin K) (r : Fin (n + 1)),
          (polyEuler^[(r : ℕ)] (windowLin N₀ (Wj j) w)).eval
            (fiberNode lam src sh t j a) = J a r :=
    fun j => exists_small_window' (hnodeinj j) (hnode0 j) (n + 1) N₀ hεpos
  choose δf hδfpos hδf using hsmall
  obtain ⟨δ, hδpos, hδle⟩ := exists_uniform_pos δf hδfpos
  obtain ⟨m₀, hm₀pos, hm₀le⟩ :=
    exists_uniform_pos (fun j : Fin L => (min 1 ‖lam j‖) ^ n) (fun j => by
      have hpos : 0 < min 1 ‖lam j‖ := lt_min one_pos (norm_pos_iff.mpr (hlam j))
      positivity)
  have hδ'pos : 0 < δ * m₀ := mul_pos hδpos hm₀pos
  have hBopen : IsOpen {Y : Fin K × (ι × Fin (n + 1)) → ℂ | ∀ q, ‖Y q - Jz q‖ < δ * m₀} := by
    have heq : {Y : Fin K × (ι × Fin (n + 1)) → ℂ | ∀ q, ‖Y q - Jz q‖ < δ * m₀} =
        ⋂ q : Fin K × (ι × Fin (n + 1)),
          (fun Y : Fin K × (ι × Fin (n + 1)) → ℂ => Y q) ⁻¹' (Metric.ball (Jz q) (δ * m₀)) := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball,
        dist_eq_norm]
    rw [heq]
    exact isOpen_iInter_of_finite fun q =>
      (continuous_apply q).isOpen_preimage _ Metric.isOpen_ball
  obtain ⟨Y, hYB, hYdet⟩ := exists_eval_ne_zero_of_isOpen hP hBopen
    ⟨Jz, fun q => by simpa using hδ'pos⟩
  have hpowle : ∀ (j : Fin L) (r : Fin (n + 1)), m₀ ≤ ‖lam j‖ ^ (r : ℕ) := by
    intro j r
    have hmin1 : min 1 ‖lam j‖ ≤ 1 := min_le_left _ _
    have hminpos : 0 < min 1 ‖lam j‖ := lt_min one_pos (norm_pos_iff.mpr (hlam j))
    have hstep1 : (min 1 ‖lam j‖) ^ n ≤ (min 1 ‖lam j‖) ^ (r : ℕ) :=
      pow_le_pow_of_le_one hminpos.le hmin1 (by omega)
    have hstep2 : (min 1 ‖lam j‖) ^ (r : ℕ) ≤ ‖lam j‖ ^ (r : ℕ) :=
      pow_le_pow_left₀ hminpos.le (min_le_right _ _) _
    exact le_trans (hm₀le j) (le_trans hstep1 hstep2)
  have hJbound : ∀ (j : Fin L) (a : srcFiber src j × Fin K) (r : Fin (n + 1)),
      ‖(Y (a.2, (a.1.val, r)) - Jz (a.2, (a.1.val, r))) / lam j ^ (r : ℕ)‖ < δf j := by
    intro j a r
    have h1 : ‖Y (a.2, (a.1.val, r)) - Jz (a.2, (a.1.val, r))‖ < δ * m₀ := hYB _
    have hpow : (0 : ℝ) < ‖lam j‖ ^ (r : ℕ) :=
      pow_pos (norm_pos_iff.mpr (hlam j)) _
    rw [norm_div, norm_pow, div_lt_iff₀ hpow]
    calc ‖Y (a.2, (a.1.val, r)) - Jz (a.2, (a.1.val, r))‖ < δ * m₀ := h1
      _ ≤ δf j * ‖lam j‖ ^ (r : ℕ) := by
          refine mul_le_mul (hδle j) (hpowle j r) hm₀pos.le (le_trans hδpos.le (hδle j))
  choose w hwnorm hwval using fun j : Fin L => hδf j
    (fun a r => (Y (a.2, (a.1.val, r)) - Jz (a.2, (a.1.val, r))) / lam j ^ (r : ℕ))
    (hJbound j)
  have hwbox : ∀ (j : Fin L) (i : Fin (Wj j)),
      ‖w j i‖ ≤ (((N₀ + (i : ℕ)).factorial : ℝ))⁻¹ := by
    intro j i
    have h2 : N₀ + (i : ℕ) ≤ N₀ + W := by
      have h3 := i.2
      have h4 := hWjle j
      omega
    have h3 : ((N₀ + (i : ℕ)).factorial : ℝ) ≤ (((N₀ + W).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le h2
    have h4 : ε ≤ (((N₀ + (i : ℕ)).factorial : ℝ))⁻¹ := by
      rw [hεdef]
      gcongr
    exact le_of_lt (lt_of_lt_of_le (hwnorm j i) h4)
  refine ⟨fun j => setWindowBox (Cz j) N₀ (Wj j) (w j) (hwbox j), ?_, ?_⟩
  · intro j k hk
    show setWindowBox (Cz j) N₀ (Wj j) (w j) (hwbox j) k = C₀ j k
    rw [setWindowBox_eq_of_lt _ _ _ _ _ hk]
    exact zeroWindowBox_eq_of_lt (C₀ j) N₀ W hk
  · refine ⟨t, ?_⟩
    have hjet : ∀ (a : Fin K) (v : Option (ι × Fin (n + 1))),
        famJetPoint (orbFun lam src sh fun j => setWindowBox (Cz j) N₀ (Wj j) (w j) (hwbox j))
          n (t a) v = blockOf t Y (a, v) := by
      intro a v
      cases v with
      | none => rfl
      | some p =>
          obtain ⟨i, r⟩ := p
          have hseq : boxSeq (setWindowBox (Cz (src i)) N₀ (Wj (src i)) (w (src i))
              (hwbox (src i))) =
              fun k => boxSeq (Cz (src i)) k + windowSeq N₀ (Wj (src i)) (w (src i)) k :=
            boxSeq_setWindowBox _ _ _ _ _
              (fun k h1 h2 => hCzzero (src i) k h1 (lt_of_lt_of_le h2 (hWjle _)))
          have hbase : ∀ k, ‖boxSeq (Cz (src i)) k‖ ≤ ((k.factorial : ℝ))⁻¹ :=
            boxSeq_bound (Cz (src i))
          have hwin : ∀ k, ‖windowSeq N₀ (Wj (src i)) (w (src i)) k‖ ≤ ((k.factorial : ℝ))⁻¹ :=
            norm_windowSeq_le (hwbox (src i)) (fun k => by positivity)
          have hsum1 := summable_jetSeries hbase (r : ℕ) (orbNode lam src sh i (t a))
          have hsum2 := summable_jetSeries hwin (r : ℕ) (orbNode lam src sh i (t a))
          have hwj := hwval (src i) (⟨i, rfl⟩, a) r
          have hnodeeq : fiberNode lam src sh t (src i) (⟨i, rfl⟩, a) =
              orbNode lam src sh i (t a) := rfl
          rw [hnodeeq] at hwj
          have hJzval : Jz (a, (i, r)) =
              lam (src i) ^ (r : ℕ) *
                jetSeriesFun (boxSeq (Cz (src i))) (r : ℕ) (orbNode lam src sh i (t a)) := by
            rw [hJzdef]
            exact iteratedDeriv_orbFun lam src sh Cz i (r : ℕ) (t a)
          have hpowne : (lam (src i)) ^ (r : ℕ) ≠ 0 := pow_ne_zero _ (hlam _)
          show iteratedDeriv (r : ℕ)
            (orbFun lam src sh (fun j => setWindowBox (Cz j) N₀ (Wj j) (w j) (hwbox j)) i)
              (t a) = Y (a, (i, r))
          rw [iteratedDeriv_orbFun, hseq,
            jetSeriesFun_add (r : ℕ) (orbNode lam src sh i (t a)) hsum1 hsum2,
            jetSeriesFun_windowSeq, hwj, mul_add, ← hJzval, mul_div_cancel₀ _ hpowne]
          ring
    have hmat : orbEvalMatrix lam src sh
        (fun j => setWindowBox (Cz j) N₀ (Wj j) (w j) (hwbox j)) M t =
        fun i a => (M i).prod fun v e => (blockOf t Y (a, v)) ^ e := by
      funext i a
      rw [orbEvalMatrix]
      exact Finsupp.prod_congr fun v _ => by rw [hjet a v]
    rw [hmat, ← eval_specDetPoly]
    exact hYdet

end

end GaloisForLFunctions.HTGeometry
