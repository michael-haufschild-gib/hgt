import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaAllPrimeStokesPairBridge
import GaloisForLFunctions.RHTower.STCPrimeWindowPackets

/-!
# The prime-height commutator has a noncompact Calkin ghost

The literal equal-depth reflection-odd Gamma exterior is minus the commutator of the diagonal
physical prime height `H = diag(h_p)`, `h_p = n log(p)/2`, with a two-channel symmetric kernel.
Recovering that kernel from its commutator is an inverse Sylvester problem, and it is not
faithful modulo compacts: using disjoint cofinal prime pairs `p_k < q_k` with vanishing height
gap (a consequence of the prime number theorem), the partial swap `X : e_{p_k} ↔ e_{q_k}` is a
bounded selfadjoint operator of norm one and essential norm at least one, it preserves the
natural domain of the unbounded `H`, and `[H,X]` extends to a compact operator.  Hence no Calkin
lower bound `‖[X]‖ ≤ C ‖[[H,X]]‖` holds.
-/

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.LpDiagonal

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### The Sylvester form of the source exterior on finite packets -/

/-- On every finite packet of primes at one depth, the literal reflection-odd exterior is
`S = -[H, Q]` with `H` the diagonal physical height and `Q` the symmetric two-channel kernel. -/
theorem sourcePacket_sylvester {m : ℕ} (c : Fin m → Nat.Primes) (e : ℕ) (g : ℝ) :
    (Matrix.of fun i j => xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
        (sourcePrimeCell (c i) e) (sourcePrimeCell (c j) e)) =
      -(Matrix.diagonal (fun i => xiGammaEulerBoundaryHalfHeight (c i) e) *
          Matrix.of (fun i j => sourcePairSymmetricKernel (c i) (c j) e g) -
        Matrix.of (fun i j => sourcePairSymmetricKernel (c i) (c j) e g) *
          Matrix.diagonal (fun i => xiGammaEulerBoundaryHalfHeight (c i) e)) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  rw [source_pair_commutator_identity]
  ring

/-! ### Disjoint cofinal prime pairs with vanishing log gap -/

/-- Interleaved prime pairs `P 0 < Q 0 < P 1 < Q 1 < ⋯` with `Q k < (1 + 1/(k+1)) P k`. -/
theorem exists_prime_swap_pairs :
    ∃ P Q : ℕ → ℕ, (∀ k, (P k).Prime ∧ (Q k).Prime) ∧ (∀ k, P k < Q k) ∧
      (∀ k, Q k < P (k + 1)) ∧ ∀ k, (Q k : ℝ) < (1 + 1 / ((k : ℝ) + 1)) * P k := by
  have hpair : ∀ k N : ℕ, ∃ pq : ℕ × ℕ, pq.1.Prime ∧ pq.2.Prime ∧ (N : ℝ) < pq.1 ∧
      pq.1 < pq.2 ∧ (pq.2 : ℝ) < (1 + 1 / ((k : ℝ) + 1)) * pq.1 := by
    intro k N
    obtain ⟨p, q, hp, hq, hN, hpq, hr⟩ :=
      exists_prime_pair_ratio_lt (ε := 1 / ((k : ℝ) + 1)) (by positivity) N
    exact ⟨(p, q), hp, hq, hN, hpq, hr⟩
  choose F hF using hpair
  let seq : ℕ → ℕ × ℕ := fun k => Nat.rec (F 0 0) (fun k pq => F (k + 1) pq.2) k
  have hseq0 : seq 0 = F 0 0 := rfl
  have hseqS : ∀ k, seq (k + 1) = F (k + 1) (seq k).2 := fun k => rfl
  have hseq : ∀ k, ∃ N, seq k = F k N := by
    intro k
    cases k with
    | zero => exact ⟨0, hseq0⟩
    | succ k => exact ⟨_, hseqS k⟩
  refine ⟨fun k => (seq k).1, fun k => (seq k).2, fun k => ?_, fun k => ?_, fun k => ?_,
    fun k => ?_⟩
  · obtain ⟨N, hN⟩ := hseq k
    dsimp only
    rw [hN]
    exact ⟨(hF _ _).1, (hF _ _).2.1⟩
  · obtain ⟨N, hN⟩ := hseq k
    dsimp only
    rw [hN]
    exact (hF _ _).2.2.2.1
  · show (seq k).2 < (seq (k + 1)).1
    rw [hseqS]
    exact_mod_cast (hF (k + 1) (seq k).2).2.2.1
  · obtain ⟨N, hN⟩ := hseq k
    dsimp only
    rw [hN]
    exact (hF _ _).2.2.2.2

/-! ### The partial swap -/

section Swap

variable {P Q : ℕ → ℕ} (hprime : ∀ k, (P k).Prime ∧ (Q k).Prime) (hPQ : ∀ k, P k < Q k)
  (hQP : ∀ k, Q k < P (k + 1))

include hPQ hQP in
private theorem P_strictMono : StrictMono P :=
  strictMono_nat_of_lt_succ fun k => (hPQ k).trans (hQP k)

include hPQ hQP in
private theorem Q_strictMono : StrictMono Q :=
  strictMono_nat_of_lt_succ fun k => (hQP k).trans (hPQ (k + 1))

include hPQ hQP in
private theorem P_ne_Q (k j : ℕ) : P k ≠ Q j := by
  intro h
  rcases le_or_gt k j with hkj | hkj
  · have := (P_strictMono hPQ hQP).monotone hkj
    have := hPQ j
    omega
  · have h1 : Q j < P (j + 1) := hQP j
    have h2 := (P_strictMono hPQ hQP).monotone (show j + 1 ≤ k by omega)
    omega

open Classical in
/-- The involution of `ℕ` exchanging `P k ↔ Q k`. -/
private def swapNat (P Q : ℕ → ℕ) (n : ℕ) : ℕ :=
  if h : ∃ k, P k = n then Q (Nat.find h) else if h' : ∃ k, Q k = n then P (Nat.find h') else n

include hPQ hQP in
private theorem swapNat_P (k : ℕ) : swapNat P Q (P k) = Q k := by
  classical
  have h : ∃ j, P j = P k := ⟨k, rfl⟩
  unfold swapNat
  rw [dif_pos h]
  congr 1
  exact (P_strictMono hPQ hQP).injective (Nat.find_spec h)

include hPQ hQP in
private theorem swapNat_Q (k : ℕ) : swapNat P Q (Q k) = P k := by
  classical
  have hn : ¬ ∃ j, P j = Q k := fun ⟨j, hj⟩ => P_ne_Q hPQ hQP j k hj
  have h : ∃ j, Q j = Q k := ⟨k, rfl⟩
  unfold swapNat
  rw [dif_neg hn, dif_pos h]
  congr 1
  exact (Q_strictMono hPQ hQP).injective (Nat.find_spec h)

private theorem swapNat_other {n : ℕ} (hP : ∀ k, P k ≠ n) (hQ : ∀ k, Q k ≠ n) :
    swapNat P Q n = n := by
  classical
  unfold swapNat
  rw [dif_neg (fun ⟨k, hk⟩ => hP k hk), dif_neg (fun ⟨k, hk⟩ => hQ k hk)]

include hPQ hQP in
private theorem swapNat_involutive : Function.Involutive (swapNat P Q) := by
  intro n
  by_cases hP : ∃ k, P k = n
  · obtain ⟨k, rfl⟩ := hP
    rw [swapNat_P hPQ hQP, swapNat_Q hPQ hQP]
  · by_cases hQ : ∃ k, Q k = n
    · obtain ⟨k, rfl⟩ := hQ
      rw [swapNat_Q hPQ hQP, swapNat_P hPQ hQP]
    · push Not at hP hQ
      rw [swapNat_other hP hQ, swapNat_other hP hQ]

include hprime hPQ hQP in
private theorem swapNat_prime (p : Nat.Primes) : (swapNat P Q p).Prime := by
  by_cases hP : ∃ k, P k = p
  · obtain ⟨k, hk⟩ := hP
    rw [← hk, swapNat_P hPQ hQP]; exact (hprime k).2
  · by_cases hQ : ∃ k, Q k = p
    · obtain ⟨k, hk⟩ := hQ
      rw [← hk, swapNat_Q hPQ hQP]; exact (hprime k).1
    · push Not at hP hQ
      rw [swapNat_other hP hQ]; exact p.property

/-- The prime involution exchanging `P k ↔ Q k`. -/
private def swapPrimes : Nat.Primes ≃ Nat.Primes where
  toFun p := ⟨swapNat P Q p, swapNat_prime hprime hPQ hQP p⟩
  invFun p := ⟨swapNat P Q p, swapNat_prime hprime hPQ hQP p⟩
  left_inv p := Subtype.ext (swapNat_involutive hPQ hQP p)
  right_inv p := Subtype.ext (swapNat_involutive hPQ hQP p)

/-- The moved primes. -/
private def swapSet (P Q : ℕ → ℕ) : Set Nat.Primes := {p | ∃ k, P k = p ∨ Q k = p}

end Swap

/-! ### The ghost theorem -/

/-- Multiplication by the physical prime height `h_p = n log(p)/2` at depth `e`. -/
def stcHeightMul (e : ℕ) (f : Nat.Primes → ℂ) (p : Nat.Primes) : ℂ :=
  (xiGammaEulerBoundaryHalfHeight p e : ℂ) * f p

/-- The natural domain of the unbounded height multiplication. -/
def stcHeightDomain (e : ℕ) : Set ℓ²P := {x | Memℓp (stcHeightMul e (x : Nat.Primes → ℂ)) 2}

/-- The height multiplication on its domain. -/
def stcHeightOp (e : ℕ) (x : ℓ²P) (hx : x ∈ stcHeightDomain e) : ℓ²P := ⟨_, hx⟩

theorem orthonormal_lpBasisVec_comp {f : ℕ → Nat.Primes} (hf : Function.Injective f) :
    Orthonormal ℂ (fun k => lpBasisVec (f k)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_lpBasisVec_right]
  by_cases h : i = j
  · subst h; simp [lpBasisVec]
  · rw [if_neg h]
    simp [lpBasisVec, lp.single_apply, Pi.single_eq_of_ne (fun h' => h (hf h'.symm))]

/-- **Calkin ghost.** At every depth there are a bounded selfadjoint operator `X` of norm one and
essential norm at least one, and a compact operator `K`, such that `X` preserves the domain of
the prime-height multiplication `H` and `H X - X H = K` on that domain. -/
theorem stc_prime_height_commutator_calkin_ghost (e : ℕ) :
    ∃ X K : ℓ²P →L[ℂ] ℓ²P,
      ¬ IsCompactOperator X ∧ IsCompactOperator K ∧ IsSelfAdjoint X ∧ ‖X‖ = 1 ∧
      1 ≤ essentialNorm X ∧ essentialNorm K = 0 ∧
      (∀ x : ℓ²P, x ∈ stcHeightDomain e → X x ∈ stcHeightDomain e) ∧
      ∀ (x : ℓ²P) (hx : x ∈ stcHeightDomain e),
        stcHeightMul e (X x : Nat.Primes → ℂ) =
          (X (stcHeightOp e x hx) : Nat.Primes → ℂ) + (K x : Nat.Primes → ℂ) := by
  classical
  obtain ⟨P, Q, hprime, hPQ, hQP, hratio⟩ := exists_prime_swap_pairs
  let pk : ℕ → Nat.Primes := fun k => ⟨P k, (hprime k).1⟩
  let qk : ℕ → Nat.Primes := fun k => ⟨Q k, (hprime k).2⟩
  set σ : Nat.Primes ≃ Nat.Primes := swapPrimes hprime hPQ hQP with hσ
  set S : Set Nat.Primes := swapSet P Q
  have hσσ : ∀ p, σ (σ p) = p := fun p => σ.left_inv p
  have hσsymm : ∀ p, σ.symm p = σ p := fun p => rfl
  have hσP : ∀ k, (σ (pk k) : ℕ) = Q k := fun k => swapNat_P hPQ hQP k
  have hσQ : ∀ k, (σ (qk k) : ℕ) = P k := fun k => swapNat_Q hPQ hQP k
  have hσout : ∀ p : Nat.Primes, p ∉ S → σ p = p := by
    intro p hp
    apply Subtype.ext
    show swapNat P Q p = p
    refine swapNat_other (fun k hk => hp ⟨k, Or.inl hk⟩) (fun k hk => hp ⟨k, Or.inr hk⟩)
  have hSσ : ∀ p, σ p ∈ S ↔ p ∈ S := by
    intro p
    constructor
    · intro h
      by_contra hp
      rw [hσout p hp] at h
      exact hp h
    · rintro ⟨k, hk | hk⟩
      · refine ⟨k, Or.inr ?_⟩
        have : p = pk k := Subtype.ext hk.symm
        rw [this, hσP]
      · refine ⟨k, Or.inl ?_⟩
        have : p = qk k := Subtype.ext hk.symm
        rw [this, hσQ]
  -- the height gap on moved primes
  let h : Nat.Primes → ℝ := fun p => xiGammaEulerBoundaryHalfHeight p e
  let ind : Nat.Primes → ℂ := fun p => if p ∈ S then 1 else 0
  let c : Nat.Primes → ℂ := fun p => ind p * ((h p : ℂ) - h (σ p))
  have hind : ∀ p, ‖ind p‖ ≤ 1 := fun p => by by_cases hp : p ∈ S <;> simp [ind, hp]
  have hgap : ∀ k, |h (qk k) - h (pk k)| ≤
      ((e : ℝ) + 1) / 2 * Real.log (1 + 1 / ((k : ℝ) + 1)) := by
    intro k
    simp only [h, xiGammaEulerBoundaryHalfHeight]
    have hP0 : (0 : ℝ) < P k := by exact_mod_cast (hprime k).1.pos
    have hlt : Real.log (P k : ℝ) < Real.log (Q k : ℝ) :=
      Real.log_lt_log hP0 (by exact_mod_cast hPQ k)
    have hup : Real.log (Q k : ℝ) ≤ Real.log ((1 + 1 / ((k : ℝ) + 1)) * P k) :=
      Real.log_le_log (by exact_mod_cast (hprime k).2.pos) (hratio k).le
    rw [Real.log_mul (by positivity) hP0.ne'] at hup
    rw [abs_of_nonneg (by nlinarith [show (0 : ℝ) ≤ ((e : ℝ) + 1) / 2 by positivity])]
    have : ((e : ℝ) + 1) / 2 * Real.log (Q k : ℝ) - ((e : ℝ) + 1) / 2 * Real.log (P k : ℝ) =
      ((e : ℝ) + 1) / 2 * (Real.log (Q k : ℝ) - Real.log (P k : ℝ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hcS : ∀ k, ‖c (pk k)‖ ≤ ((e : ℝ) + 1) / 2 * Real.log (1 + 1 / ((k : ℝ) + 1))
      ∧ ‖c (qk k)‖ ≤ ((e : ℝ) + 1) / 2 * Real.log (1 + 1 / ((k : ℝ) + 1)) := by
    intro k
    have hPS : pk k ∈ S := ⟨k, Or.inl rfl⟩
    have hQS : qk k ∈ S := ⟨k, Or.inr rfl⟩
    have e1 : σ (pk k) = qk k := Subtype.ext (hσP k)
    have e2 : σ (qk k) = pk k := Subtype.ext (hσQ k)
    constructor
    · simp only [c, ind, if_pos hPS, one_mul, e1]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hgap k
    · simp only [c, ind, if_pos hQS, one_mul, e2]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hgap k
  have hlog2 : ∀ k : ℕ, Real.log (1 + 1 / ((k : ℝ) + 1)) ≤ Real.log 2 := fun k =>
    Real.log_le_log (by positivity) (by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith)
  set M : ℝ := ((e : ℝ) + 1) / 2 * Real.log 2
  have hM : 0 ≤ M := by positivity
  have hc : ∀ p, ‖c p‖ ≤ M := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨k, hk | hk⟩ := hp
      · have : p = pk k := Subtype.ext hk.symm
        rw [this]
        exact (hcS k).1.trans (mul_le_mul_of_nonneg_left (hlog2 k) (by positivity))
      · have : p = qk k := Subtype.ext hk.symm
        rw [this]
        exact (hcS k).2.trans (mul_le_mul_of_nonneg_left (hlog2 k) (by positivity))
    · simp [c, ind, hp, hM]
  have hshrink : Tendsto (fun k : ℕ => ((e : ℝ) + 1) / 2 * Real.log (1 + 1 / ((k : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp h1
    simp only [Function.comp_def, add_zero, Real.log_one] at h2
    simpa using h2.const_mul (((e : ℝ) + 1) / 2)
  have hclim : Tendsto (fun p => ‖c p‖) cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K0, hK0⟩ := eventually_atTop.mp (hshrink.eventually (gt_mem_nhds hε))
    have hfin : {p : Nat.Primes | ∃ k < K0, P k = p ∨ Q k = p}.Finite := by
      have : {p : Nat.Primes | ∃ k < K0, P k = p ∨ Q k = p} ⊆
          ↑((Finset.range K0).biUnion (fun k => ({pk k, qk k} : Finset Nat.Primes))) := by
        rintro p ⟨k, hk, hk' | hk'⟩
        · simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
            Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact ⟨k, hk, Or.inl (Subtype.ext hk'.symm)⟩
        · simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
            Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact ⟨k, hk, Or.inr (Subtype.ext hk'.symm)⟩
      exact (Finset.finite_toSet _).subset this
    filter_upwards [hfin.compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and] at hp
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_cases hpS : p ∈ S
    · obtain ⟨k, hk | hk⟩ := hpS
      · have hkK : K0 ≤ k := by by_contra hlt; exact hp k (by omega) (Or.inl hk)
        have : p = pk k := Subtype.ext hk.symm
        rw [this]
        exact lt_of_le_of_lt (hcS k).1 (hK0 k hkK)
      · have hkK : K0 ≤ k := by by_contra hlt; exact hp k (by omega) (Or.inr hk)
        have : p = qk k := Subtype.ext hk.symm
        rw [this]
        exact lt_of_le_of_lt (hcS k).2 (hK0 k hkK)
    · simp [c, ind, hpS, hε]
  -- the operators
  let R := lpReindexCLM σ
  let X : ℓ²P →L[ℂ] ℓ²P := lpDiag ind 1 zero_le_one hind ∘L R
  let K : ℓ²P →L[ℂ] ℓ²P := lpDiag c M hM hc ∘L R
  have hXc : ∀ x p, (X x : Nat.Primes → ℂ) p = ind p * (x : Nat.Primes → ℂ) (σ p) := by
    intro x p; rfl
  have hKc : ∀ x p, (K x : Nat.Primes → ℂ) p = c p * (x : Nat.Primes → ℂ) (σ p) := by
    intro x p; rfl
  -- the swap on basis vectors
  have hXe : ∀ k, X (lpBasisVec (pk k)) = lpBasisVec (qk k) := by
    intro k
    ext p
    rw [hXc]
    simp only [lpBasisVec, lp.single_apply]
    by_cases hp : p = qk k
    · subst hp
      have e2 : σ (qk k) = pk k := Subtype.ext (hσQ k)
      simp [ind, e2, show (qk k) ∈ S from ⟨k, Or.inr rfl⟩]
    · have hne : σ p ≠ pk k := by
        intro h'
        apply hp
        have := congrArg σ h'
        rw [hσσ] at this
        rw [this]
        exact Subtype.ext (hσP k)
      simp [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hne]
  have horth : Orthonormal ℂ (fun k => lpBasisVec (pk k)) :=
    orthonormal_lpBasisVec_comp (fun a b hab =>
      (P_strictMono hPQ hQP).injective (congrArg Subtype.val hab))
  have hnormX : ‖X‖ ≤ 1 := by
    calc ‖X‖ ≤ ‖lpDiag ind 1 zero_le_one hind‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact norm_lpDiag_le _ _ _ _
          · exact (lpReindex σ).toLinearIsometry.norm_toContinuousLinearMap_le
      _ = 1 := by norm_num
  have hbasis_norm : ∀ q : Nat.Primes, ‖lpBasisVec q‖ = 1 := fun q => by
    rw [lpBasisVec, lp.norm_single (by norm_num), norm_one]
  -- essential norm of X
  have hess : 1 ≤ essentialNorm X := by
    refine le_essentialNorm X 1 fun K' hK' => ?_
    have hK0 := IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal K' hK' horth
    have hlow : ∀ k, 1 - ‖K' (lpBasisVec (pk k))‖ ≤ ‖X - K'‖ := by
      intro k
      have h1 := (X - K').le_opNorm (lpBasisVec (pk k))
      rw [hbasis_norm, mul_one, sub_apply, hXe] at h1
      have h2 := norm_sub_norm_le (lpBasisVec (qk k))
        (K' (lpBasisVec (pk k)))
      rw [hbasis_norm] at h2
      linarith
    have hlim : Tendsto (fun k => 1 - ‖K' (lpBasisVec (pk k))‖)
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hK0
    rw [sub_zero] at hlim
    exact le_of_tendsto hlim (Eventually.of_forall hlow)
  have hXnc : ¬ IsCompactOperator X := by
    intro hX
    have := essentialNorm_eq_zero_of_isCompactOperator hX
    linarith
  have hKc' : IsCompactOperator K :=
    (isCompactOperator_lpDiag c M hM hc hclim).comp_clm R
  refine ⟨X, K, hXnc, hKc', ?_, ?_, hess, essentialNorm_eq_zero_of_isCompactOperator hKc',
    ?_, ?_⟩
  · -- selfadjointness
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp only [ContinuousLinearMap.coe_coe]
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    rw [← σ.tsum_eq (fun p => ⟪(x : Nat.Primes → ℂ) p, (X y : Nat.Primes → ℂ) p⟫_ℂ)]
    refine tsum_congr fun p => ?_
    rw [hXc, hXc, hσσ]
    have hi : ind (σ p) = ind p := by
      simp only [ind]
      by_cases hp : p ∈ S
      · rw [if_pos ((hSσ p).mpr hp), if_pos hp]
      · rw [if_neg (fun h' => hp ((hSσ p).mp h')), if_neg hp]
    rw [hi]
    by_cases hp : p ∈ S <;> simp [ind, hp]
  · -- norm one
    refine le_antisymm hnormX ?_
    have h1 := X.le_opNorm (lpBasisVec (pk 0))
    rw [hXe, hbasis_norm, hbasis_norm, mul_one] at h1
    exact h1
  · -- domain invariance
    intro x hx
    have hsum : Memℓp (fun p => (X (stcHeightOp e x hx) : Nat.Primes → ℂ) p +
        (K x : Nat.Primes → ℂ) p) 2 :=
      (lp.memℓp (X (stcHeightOp e x hx))).add (lp.memℓp (K x))
    have heq : stcHeightMul e (X x : Nat.Primes → ℂ) = fun p =>
        (X (stcHeightOp e x hx) : Nat.Primes → ℂ) p + (K x : Nat.Primes → ℂ) p := by
      funext p
      simp only [stcHeightMul, hXc, hKc, stcHeightOp, c]
      show (h p : ℂ) * (ind p * (x : Nat.Primes → ℂ) (σ p)) =
        ind p * ((h (σ p) : ℂ) * (x : Nat.Primes → ℂ) (σ p)) +
          ind p * ((h p : ℂ) - h (σ p)) * (x : Nat.Primes → ℂ) (σ p)
      ring
    show Memℓp (stcHeightMul e (X x : Nat.Primes → ℂ)) 2
    rw [heq]
    exact hsum
  · -- the commutator identity
    intro x hx
    funext p
    simp only [stcHeightMul, Pi.add_apply, hXc, hKc, stcHeightOp, c]
    show (h p : ℂ) * (ind p * (x : Nat.Primes → ℂ) (σ p)) =
      ind p * ((h (σ p) : ℂ) * (x : Nat.Primes → ℂ) (σ p)) +
        ind p * ((h p : ℂ) - h (σ p)) * (x : Nat.Primes → ℂ) (σ p)
    ring

/-- **No Calkin inverse of the prime-height derivation.** There is no constant `C` bounding the
essential norm of every domain-preserving bounded operator by `C` times the essential norm of
a bounded extension of its height commutator. -/
theorem no_calkin_lower_bound_prime_height_commutator (e : ℕ) :
    ¬ ∃ C : ℝ, ∀ X K : ℓ²P →L[ℂ] ℓ²P,
      (∀ x : ℓ²P, x ∈ stcHeightDomain e → X x ∈ stcHeightDomain e) →
      (∀ (x : ℓ²P) (hx : x ∈ stcHeightDomain e),
        stcHeightMul e (X x : Nat.Primes → ℂ) =
          (X (stcHeightOp e x hx) : Nat.Primes → ℂ) + (K x : Nat.Primes → ℂ)) →
      essentialNorm X ≤ C * essentialNorm K := by
  rintro ⟨C, hC⟩
  obtain ⟨X, K, -, -, -, -, hess, hK, hdom, hcomm⟩ := stc_prime_height_commutator_calkin_ghost e
  have := hC X K hdom hcomm
  rw [hK, mul_zero] at this
  linarith

end

end RHTower
