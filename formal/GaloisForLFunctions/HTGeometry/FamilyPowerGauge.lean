import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# The power gauge for finite families

Raising every member of a finite family to a fixed positive power creates no differential relation:
a relation among the powers pulls back to a relation among the family itself.

The jet substitution is the formal Leibniz recursion for the derivatives of `y ^ N`.  Blockwise it
is triangular in the jet variables with diagonal `N y_0 ^ (N - 1)`, and its zeroth equation
`y_0 ^ N = w_0` is solvable because `ℂ` is algebraically closed.  So the induced point map covers
the locus where no zeroth jet vanishes, and the substitution kills no nonzero polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The scalar Leibniz recursion for the jets of an `N`-th power: `powJetScalar y N k` is the `k`-th
derivative of `f ^ N` expressed in the jets `y j = f ^ (j)`. -/
def powJetScalar (y : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | (N + 1), k =>
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : ℂ) * y j * powJetScalar y N (k - j)

theorem powJetScalar_zero (y : ℕ → ℂ) (k : ℕ) :
    powJetScalar y 0 k = if k = 0 then 1 else 0 := rfl

theorem powJetScalar_succ (y : ℕ → ℂ) (N k : ℕ) :
    powJetScalar y (N + 1) k
      = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : ℂ) * y j * powJetScalar y N (k - j) := rfl

/-- The zeroth formal jet of a power is the power of the zeroth jet. -/
theorem powJetScalar_zeroth (y : ℕ → ℂ) (N : ℕ) : powJetScalar y N 0 = y 0 ^ N := by
  induction N with
  | zero => simp [powJetScalar_zero]
  | succ N ih =>
      rw [powJetScalar_succ, Finset.sum_range_one, ih]
      simp [pow_succ]
      ring

/-- The `k`-th formal jet of a power depends only on the jets up to order `k`. -/
theorem powJetScalar_congr (y y' : ℕ → ℂ) (N : ℕ) :
    ∀ k, (∀ j, j ≤ k → y j = y' j) → powJetScalar y N k = powJetScalar y' N k := by
  induction N with
  | zero => intro k _; rfl
  | succ N ih =>
      intro k h
      rw [powJetScalar_succ, powJetScalar_succ]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [h j (by omega), ih (k - j) fun l hl => h l (by omega)]

theorem natCast_mul_mul_pow_pred (c : ℂ) (N : ℕ) :
    (N : ℂ) * (c * c ^ (N - 1)) = (N : ℂ) * c ^ N := by
  cases N with
  | zero => simp
  | succ N => rw [Nat.add_sub_cancel, ← pow_succ']

/-- **The formal power jets are triangular.**  Beyond the diagonal term `N y_0 ^ (N - 1) y_k`, the
`k`-th formal jet of a power depends only on the jets of order strictly below `k`. -/
theorem powJetScalar_succ_sub_diagonal (N : ℕ) :
    ∀ (k : ℕ) (y y' : ℕ → ℂ), (∀ j, j ≤ k → y j = y' j) →
      powJetScalar y N (k + 1) - (N : ℂ) * y 0 ^ (N - 1) * y (k + 1)
        = powJetScalar y' N (k + 1) - (N : ℂ) * y' 0 ^ (N - 1) * y' (k + 1) := by
  induction N with
  | zero =>
      intro k y y' _
      simp [powJetScalar_zero]
  | succ N ih =>
      intro k y y' h
      have hexp : ∀ z : ℕ → ℂ, powJetScalar z (N + 1) (k + 1)
          = (∑ j ∈ Finset.range k,
              (((k + 1).choose (j + 1) : ℕ) : ℂ) * z (j + 1) * powJetScalar z N (k - j))
            + z 0 * powJetScalar z N (k + 1) + z (k + 1) * z 0 ^ N := by
        intro z
        rw [powJetScalar_succ, Finset.sum_range_succ, Finset.sum_range_succ']
        have h1 : (((k + 1).choose (k + 1) : ℕ) : ℂ) * z (k + 1)
              * powJetScalar z N (k + 1 - (k + 1))
            = z (k + 1) * z 0 ^ N := by
          rw [Nat.choose_self, Nat.sub_self, powJetScalar_zeroth]
          norm_num
        have h2 : (((k + 1).choose 0 : ℕ) : ℂ) * z 0 * powJetScalar z N (k + 1 - 0)
            = z 0 * powJetScalar z N (k + 1) := by
          rw [Nat.choose_zero_right, Nat.sub_zero]
          norm_num
        have h3 : ∀ j ∈ Finset.range k,
            (((k + 1).choose (j + 1) : ℕ) : ℂ) * z (j + 1) * powJetScalar z N (k + 1 - (j + 1))
              = (((k + 1).choose (j + 1) : ℕ) : ℂ) * z (j + 1) * powJetScalar z N (k - j) := by
          intro j _
          rw [Nat.succ_sub_succ]
        rw [Finset.sum_congr rfl h3, h1, h2]
      have hmid : (∑ j ∈ Finset.range k,
            (((k + 1).choose (j + 1) : ℕ) : ℂ) * y (j + 1) * powJetScalar y N (k - j))
          = ∑ j ∈ Finset.range k,
            (((k + 1).choose (j + 1) : ℕ) : ℂ) * y' (j + 1) * powJetScalar y' N (k - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [h (j + 1) (by omega), powJetScalar_congr y y' N (k - j) fun l hl => h l (by omega)]
      have hy0 : y 0 = y' 0 := h 0 (Nat.zero_le k)
      have hIH := ih k y y' h
      rw [hy0] at hIH
      rw [hexp y, hexp y', hmid, hy0]
      simp only [Nat.add_sub_cancel]
      push_cast
      linear_combination y' 0 * hIH + (y (k + 1) - y' (k + 1)) * natCast_mul_mul_pow_pred (y' 0) N

/-- **The formal power jets are surjective off the zeroth jet.**  Every jet packet whose zeroth
entry is nonzero is the packet of formal power jets of some packet. -/
theorem exists_powJetScalar_eq {N : ℕ} (hN : N ≠ 0) (W : ℕ → ℂ) (hW : W 0 ≠ 0) :
    ∃ v : ℕ → ℂ, ∀ k, powJetScalar v N k = W k := by
  classical
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_pow_nat_eq (W 0) (Nat.pos_of_ne_zero hN)
  have hy₀ne : y₀ ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hN] at hy₀
    exact hW hy₀.symm
  have hdne : (N : ℂ) * y₀ ^ (N - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hN) (pow_ne_zero _ hy₀ne)
  set ext : (ℕ → ℂ) → ℕ → ℂ := fun u j => if j = 0 then y₀ else u (j - 1) with hext
  have hext0 : ∀ u, ext u 0 = y₀ := by intro u; simp [hext]
  have hextsucc : ∀ (u : ℕ → ℂ) (j : ℕ), ext u (j + 1) = u j := by intro u j; simp [hext]
  have hL : ∀ (k : ℕ) (u u' : ℕ → ℂ), (∀ j, j < k → u j = u' j) →
      powJetScalar (ext u) N (k + 1) - (N : ℂ) * y₀ ^ (N - 1) * u k
        = powJetScalar (ext u') N (k + 1) - (N : ℂ) * y₀ ^ (N - 1) * u' k := by
    intro k u u' hagree
    have hcoord : ∀ j, j ≤ k → ext u j = ext u' j := by
      intro j hj
      cases j with
      | zero => rw [hext0, hext0]
      | succ l => rw [hextsucc, hextsucc, hagree l (by omega)]
    have := powJetScalar_succ_sub_diagonal N k (ext u) (ext u') hcoord
    rwa [hext0, hext0, hextsucc, hextsucc] at this
  obtain ⟨u, hu⟩ := exists_triangular_solution hdne
    (fun k u => powJetScalar (ext u) N (k + 1) - (N : ℂ) * y₀ ^ (N - 1) * u k) hL
    (fun k => W (k + 1))
  refine ⟨ext u, ?_⟩
  intro k
  cases k with
  | zero =>
      rw [powJetScalar_zeroth, hext0]
      exact hy₀
  | succ k =>
      have hk := hu k
      linear_combination hk

/-- The jet coordinates of one block of a jet packet, read as a sequence. -/
def blockJetSeq {m n : ℕ} (v : FamilyJetIndex m n → ℂ) (i : Fin m) : ℕ → ℂ :=
  fun j => if h : j < n + 1 then v (Sum.inr (i, ⟨j, h⟩)) else 0

/-- The formal jet polynomial of an `N`-th power in the jet variables of one block. -/
def powJetPoly (m n : ℕ) (i : Fin m) : ℕ → ℕ → MvPolynomial (FamilyJetIndex m n) ℂ
  | 0, k => if k = 0 then 1 else 0
  | (N + 1), k =>
      ∑ j ∈ Finset.range (k + 1),
        MvPolynomial.C ((k.choose j : ℕ) : ℂ) * familyJetVariable m n i j
          * powJetPoly m n i N (k - j)

theorem powJetPoly_zero (m n : ℕ) (i : Fin m) (k : ℕ) :
    powJetPoly m n i 0 k = if k = 0 then 1 else 0 := rfl

theorem powJetPoly_succ (m n : ℕ) (i : Fin m) (N k : ℕ) :
    powJetPoly m n i (N + 1) k
      = ∑ j ∈ Finset.range (k + 1),
          MvPolynomial.C ((k.choose j : ℕ) : ℂ) * familyJetVariable m n i j
            * powJetPoly m n i N (k - j) := rfl

/-- The jet polynomial evaluates to the scalar recursion on the block's jet coordinates. -/
theorem eval_powJetPoly {m n : ℕ} (i : Fin m) (v : FamilyJetIndex m n → ℂ) (N : ℕ) :
    ∀ k, k < n + 1 →
      MvPolynomial.eval v (powJetPoly m n i N k) = powJetScalar (blockJetSeq v i) N k := by
  induction N with
  | zero =>
      intro k _
      rw [powJetPoly_zero, powJetScalar_zero]
      split_ifs <;> simp
  | succ N ih =>
      intro k hk
      rw [powJetPoly_succ, powJetScalar_succ, map_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hjn : j < n + 1 := by omega
      rw [map_mul, map_mul, MvPolynomial.eval_C, eval_familyJetVariable_of_lt _ _ hjn,
        ih (k - j) (by omega)]
      congr 1
      congr 1
      simp [blockJetSeq, hjn]

/-- Coordinate images of the blockwise power substitution. -/
def familyPowJetImage (m n N : ℕ) : FamilyJetIndex m n → MvPolynomial (FamilyJetIndex m n) ℂ :=
  Sum.elim (fun _ => MvPolynomial.X (Sum.inl ())) fun p => powJetPoly m n p.1 N (p.2 : ℕ)

/-- The scalar recursion computes the derivatives of a power. -/
theorem powJetScalar_iteratedDeriv {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℂ (⊤ : ℕ∞) g z) (N : ℕ) :
    ∀ k, powJetScalar (fun j => iteratedDeriv j g z) N k
      = iteratedDeriv k (fun w => g w ^ N) z := by
  induction N with
  | zero =>
      intro k
      rw [powJetScalar_zero]
      simp only [pow_zero]
      cases k with
      | zero => simp
      | succ k => simp [iteratedDeriv_succ']
  | succ N ih =>
      intro k
      have hfun : (fun w => g w ^ (N + 1)) = fun w => g w * g w ^ N := by
        funext w
        rw [pow_succ']
      have hgk : ContDiffAt ℂ ((k : ℕ) : ℕ∞) g z :=
        hg.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
      have hpk : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w => g w ^ N) z := hgk.pow N
      rw [hfun, iteratedDeriv_fun_mul hgk hpk, powJetScalar_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih (k - j)]

/-- The point map of the power substitution carries the jets of a family to the jets of its
componentwise powers. -/
theorem bindPointMap_familyPowJetImage {m n N : ℕ} (g : Fin m → ℂ → ℂ) {z : ℂ}
    (hg : ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) :
    bindPointMap (familyPowJetImage m n N) (familyJetVec (m := m) (n := n) g z)
      = familyJetVec (m := m) (n := n) (fun i w => g i w ^ N) z := by
  funext s
  cases s with
  | inl x =>
      cases x
      simp [bindPointMap, familyPowJetImage, familyJetVec]
  | inr p =>
      obtain ⟨i, k⟩ := p
      show MvPolynomial.eval _ (powJetPoly m n i N (k : ℕ)) = _
      rw [eval_powJetPoly i _ N (k : ℕ) k.isLt]
      rw [powJetScalar_congr _ (fun j => iteratedDeriv j (g i) z) N (k : ℕ) ?_]
      · exact powJetScalar_iteratedDeriv (hg i) N (k : ℕ)
      · intro j hj
        have hjn : j < n + 1 := lt_of_le_of_lt hj k.isLt
        simp [blockJetSeq, hjn, familyJetVec]

/-- The point map of the power substitution covers every packet whose zeroth jets are nonzero. -/
theorem exists_familyPowJetImage_preimage {m n N : ℕ} (hN : N ≠ 0)
    (w : FamilyJetIndex m n → ℂ) (hw : ∀ i, w (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0) :
    ∃ v, bindPointMap (familyPowJetImage m n N) v = w := by
  classical
  have hzero : ∀ i : Fin m, blockJetSeq w i 0 ≠ 0 := by
    intro i
    simpa [blockJetSeq] using hw i
  choose V hV using fun i : Fin m => exists_powJetScalar_eq hN (blockJetSeq w i) (hzero i)
  refine ⟨Sum.elim (fun _ => w (Sum.inl ())) fun p => V p.1 (p.2 : ℕ), ?_⟩
  funext s
  cases s with
  | inl x =>
      cases x
      simp [bindPointMap, familyPowJetImage]
  | inr p =>
      obtain ⟨i, k⟩ := p
      show MvPolynomial.eval _ (powJetPoly m n i N (k : ℕ)) = _
      rw [eval_powJetPoly i _ N (k : ℕ) k.isLt]
      rw [powJetScalar_congr _ (V i) N (k : ℕ) ?_, hV i (k : ℕ)]
      · simp [blockJetSeq, k.isLt]
      · intro j hj
        have hjn : j < n + 1 := lt_of_le_of_lt hj k.isLt
        simp [blockJetSeq, hjn]

/-- The power substitution kills no nonzero polynomial. -/
theorem familyPow_bind₁_ne_zero {m n N : ℕ} (hN : N ≠ 0)
    {P : MvPolynomial (FamilyJetIndex m n) ℂ} (hP : P ≠ 0) :
    MvPolynomial.bind₁ (familyPowJetImage m n N) P ≠ 0 := by
  classical
  refine bind₁_ne_zero_of_pointMap_surjective _
    (∏ i : Fin m, MvPolynomial.X (Sum.inr (i, (0 : Fin (n + 1))))) ?_ ?_ hP
  · exact Finset.prod_ne_zero_iff.2 fun i _ => MvPolynomial.X_ne_zero _
  · intro w hw
    refine exists_familyPowJetImage_preimage hN w fun i => ?_
    rw [map_prod] at hw
    have hi := Finset.prod_ne_zero_iff.1 hw i (Finset.mem_univ i)
    simpa using hi

/-- **The power gauge.**  A differential relation among the `N`-th powers of a smooth family pulls
back to a differential relation among the family itself. -/
theorem familyDifferentiallyAlgebraicOn_of_pow {m : ℕ} {U : Set ℂ} (g : Fin m → ℂ → ℂ)
    {N : ℕ} (hN : N ≠ 0)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : FamilyDifferentiallyAlgebraicOn (fun i w => g i w ^ N) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, MvPolynomial.bind₁ (familyPowJetImage m n N) P, familyPow_bind₁_ne_zero hN hP, ?_⟩
  intro z hz
  rw [eval_bind₁_eq, bindPointMap_familyPowJetImage g fun i => hg z hz i]
  exact hrel z hz

/-- **Powers preserve differential independence.**  If a smooth family satisfies no differential
relation on `U`, neither does the family of its `N`-th powers. -/
theorem not_familyDifferentiallyAlgebraicOn_pow {m : ℕ} {U : Set ℂ} (g : Fin m → ℂ → ℂ)
    {N : ℕ} (hN : N ≠ 0)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i w => g i w ^ N) U :=
  fun hpow => h (familyDifferentiallyAlgebraicOn_of_pow g hN hg hpow)

/-- **Powers of a differentially independent translation family stay independent.**  If finitely
many translates of `G` satisfy no differential relation, neither do their `N`-th powers. -/
theorem not_familyDifferentiallyAlgebraicOn_translates_pow {m : ℕ} {U : Set ℂ} (G : ℂ → ℂ)
    (t : Fin m → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hG : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => G (w + t i)) z)
    (h : ¬ FamilyDifferentiallyAlgebraicOn (fun i w => G (w + t i)) U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i w => G (w + t i) ^ N) U :=
  not_familyDifferentiallyAlgebraicOn_pow _ hN hG h

/-- The jet index of a one-member family is the jet index of a single function. -/
def singleFamilyJetEquiv (n : ℕ) : FamilyJetIndex 1 n ≃ Fin (n + 2) where
  toFun := Sum.elim (fun _ => 0) fun p => (p.2).succ
  invFun := fun s => Fin.cases (Sum.inl ()) (fun j => Sum.inr (0, j)) s
  left_inv := by
    intro s
    cases s with
    | inl x => cases x; simp
    | inr p =>
        obtain ⟨i, j⟩ := p
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        simp
  right_inv := by
    intro s
    induction s using Fin.cases with
    | zero => simp
    | succ j => simp

theorem familyJetVec_one_comp (f : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    familyJetVec (m := 1) (n := n) (fun _ => f) z
      = (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) : Fin (n + 2) → ℂ)
        ∘ singleFamilyJetEquiv n := by
  funext s
  cases s with
  | inl x =>
      cases x
      simp [familyJetVec, singleFamilyJetEquiv]
  | inr p =>
      obtain ⟨i, j⟩ := p
      simp [familyJetVec, singleFamilyJetEquiv]

/-- A one-member family has a differential relation exactly when its single function does. -/
theorem familyDifferentiallyAlgebraicOn_one_iff (f : ℂ → ℂ) (U : Set ℂ) :
    FamilyDifferentiallyAlgebraicOn (fun _ : Fin 1 => f) U ↔ DifferentiallyAlgebraicOn f U := by
  constructor
  · rintro ⟨n, P, hP, hrel⟩
    refine ⟨n, MvPolynomial.rename (singleFamilyJetEquiv n) P, ?_, ?_⟩
    · exact fun hzero => hP (MvPolynomial.rename_injective _
        (singleFamilyJetEquiv n).injective (by simpa using hzero))
    · intro z hz
      rw [MvPolynomial.eval_rename, ← familyJetVec_one_comp]
      exact hrel z hz
  · rintro ⟨n, Q, hQ, hrel⟩
    refine ⟨n, MvPolynomial.rename (singleFamilyJetEquiv n).symm Q, ?_, ?_⟩
    · exact fun hzero => hQ (MvPolynomial.rename_injective _
        (singleFamilyJetEquiv n).symm.injective (by simpa using hzero))
    · intro z hz
      rw [MvPolynomial.eval_rename]
      have hcomp : familyJetVec (m := 1) (n := n) (fun _ => f) z ∘ (singleFamilyJetEquiv n).symm
          = Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z := by
        rw [familyJetVec_one_comp]
        funext s
        simp
      rw [hcomp]
      exact hrel z hz

/-- **The single-function power gauge.**  A function whose `N`-th power satisfies an algebraic
differential equation satisfies one itself. -/
theorem differentiallyAlgebraicOn_of_pow {f : ℂ → ℂ} {U : Set ℂ} {N : ℕ} (hN : N ≠ 0)
    (hf : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f z)
    (h : DifferentiallyAlgebraicOn (fun z => f z ^ N) U) :
    DifferentiallyAlgebraicOn f U := by
  rw [← familyDifferentiallyAlgebraicOn_one_iff] at h ⊢
  exact familyDifferentiallyAlgebraicOn_of_pow (fun _ : Fin 1 => f) hN
    (fun z hz _ => hf z hz) h

/-- **Hypertranscendence passes to powers.**  If a function satisfies no algebraic differential
equation on `U`, neither does any of its positive powers. -/
theorem not_differentiallyAlgebraicOn_pow {f : ℂ → ℂ} {U : Set ℂ} {N : ℕ} (hN : N ≠ 0)
    (hf : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f z)
    (h : ¬ DifferentiallyAlgebraicOn f U) :
    ¬ DifferentiallyAlgebraicOn (fun z => f z ^ N) U :=
  fun hpow => h (differentiallyAlgebraicOn_of_pow hN hf hpow)

end

end GaloisForLFunctions.HTGeometry
