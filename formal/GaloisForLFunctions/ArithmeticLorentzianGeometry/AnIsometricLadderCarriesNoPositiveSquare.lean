import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHessianOfALorentzianPolynomialTricklesDown

/-!
# An isometric ladder carries no positive square

Over `𝔽_q`, Frobenius acts on its ladder conformally with factor `q`, and the ladder Gram grows
along the ladder. Over `ℤ` the dilations are isometries: a ladder of translates `g(· − k log p)`
has a Gram depending only on the lag, a symmetric Toeplitz matrix `T_K = (c_{|i−j|})_{i,j<K}`
(`toeplitzLadder`). For Metzler couplings `c_k ≥ 0` (`k ≥ 1`):

* **Row sums** (`qf_toeplitzLadder_nonpos`): if `c_0 + 2 Σ_{1 ≤ k ≤ n} c_k ≤ 0` for all `n`, every
  depth is negative semidefinite — the stability regime with the weight `1`.
* **Two far copies** (`not_isHyperbolic_toeplitzLadder`): if the couplings decay, `c_k → 0`, and
  some depth has a positive square, then a deeper ladder has two: a vector and its translate far
  along the ladder are almost orthogonal.
* **Characterization** (`forall_isHyperbolic_toeplitzLadder_iff`): for decaying Metzler couplings
  the ladder has the Hodge index at every depth iff it is negative semidefinite at every depth.

* **Conformal ladders** (`diagConj_conformalLadder`, `forall_isHyperbolic_conformalLadder_iff`): a
  ladder with the conformal law of Frobenius, `G_{i+1,j+1} = λ G_{ij}`, is `G_{ij} = λ^{min(i,j)} a_{|i−j|}`
  (`conformalLadder`); the congruence `diag(λ^{−i/2})` turns it into the Toeplitz ladder of the
  normalized couplings `λ^{−k/2} a_k`. If these decay, it too holds its Hodge index only in the
  stability regime. Frobenius ladders escape because their normalized couplings grow like
  `q^{k/2}`.

An isometric ladder with decaying couplings therefore holds its Hodge index only in the stability
regime: the single positive square must come from outside the ladder — the pole plane — or from
couplings that grow along it, as Frobenius's do with the factor `q`. The prime pairing of atoms of
fixed width does not decay along a `p`-ladder: at lag `k log p` it sees the integers within a factor
`e^{±w}` of `p^k`, of total weight `≍ w p^{k/2}`, the main term of the prime number theorem, which
grows like the conformal weight of the pole plane.
-/

noncomputable section

open Matrix Finset Filter

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

/-- The symmetric Toeplitz ladder `T_K = (c_{|i−j|})_{i,j<K}`. -/
def toeplitzLadder (c : ℕ → ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i j => c (Nat.dist i j)

theorem toeplitzLadder_isSymm (c : ℕ → ℝ) (K : ℕ) : (toeplitzLadder c K).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [toeplitzLadder, Matrix.of_apply, Nat.dist_comm]

theorem toeplitzLadder_isMetzler {c : ℕ → ℝ} (hc : ∀ k, 1 ≤ k → 0 ≤ c k) (K : ℕ) :
    IsMetzler (toeplitzLadder c K) := fun i j hij => by
  refine hc _ ?_
  have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  unfold Nat.dist
  omega

/-! ### The stability regime -/

/-- A row of the ladder is at most `c_0 + 2 Σ_{1 ≤ k ≤ K} c_k`. -/
theorem sum_toeplitz_row_le {c : ℕ → ℝ} (hc : ∀ k, 1 ≤ k → 0 ≤ c k) {K : ℕ} (i : Fin K) :
    ∑ j : Fin K, c (Nat.dist i j) ≤ c 0 + 2 * ∑ k ∈ Icc 1 K, c k := by
  have hi : (i : ℕ) < K := i.2
  rw [Fin.sum_univ_eq_sum_range (fun j => c (Nat.dist i j)) K,
    ← Finset.sum_range_add_sum_Ico _ (show (i : ℕ) + 1 ≤ K by omega), Finset.sum_range_succ,
    Nat.dist_self]
  have hS0 : ∀ s ⊆ Icc 1 K, ∑ k ∈ s, c k ≤ ∑ k ∈ Icc 1 K, c k := fun s hs =>
    Finset.sum_le_sum_of_subset_of_nonneg hs fun k hk _ => hc k (Finset.mem_Icc.mp hk).1
  -- lags below the diagonal
  have hlow : ∑ j ∈ range i, c (Nat.dist i j) ≤ ∑ k ∈ Icc 1 K, c k := by
    have e : ∑ j ∈ range i, c (Nat.dist i j) = ∑ k ∈ (range i).image (fun j => (i : ℕ) - j), c k := by
      rw [Finset.sum_image fun x hx y hy h => by
        simp only [Finset.mem_coe, Finset.mem_range] at hx hy; omega]
      refine sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      unfold Nat.dist; congr 1; omega
    rw [e]
    refine hS0 _ fun k hk => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  -- lags above the diagonal
  have hup : ∑ j ∈ Ico ((i : ℕ) + 1) K, c (Nat.dist i j) ≤ ∑ k ∈ Icc 1 K, c k := by
    have e : ∑ j ∈ Ico ((i : ℕ) + 1) K, c (Nat.dist i j) =
        ∑ k ∈ (Ico ((i : ℕ) + 1) K).image (fun j => j - (i : ℕ)), c k := by
      rw [Finset.sum_image fun x hx y hy h => by
        simp only [Finset.mem_coe, Finset.mem_Ico] at hx hy; omega]
      refine sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Ico] at hj
      unfold Nat.dist; congr 1; omega
    rw [e]
    refine hS0 _ fun k hk => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_Ico] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  linarith

/-- **The stability regime of a ladder**: if `c_0 + 2 Σ_{1 ≤ k ≤ n} c_k ≤ 0` for every `n`, every
depth of the ladder is negative semidefinite. -/
theorem qf_toeplitzLadder_nonpos {c : ℕ → ℝ} (hc : ∀ k, 1 ≤ k → 0 ≤ c k)
    (hσ : ∀ n, c 0 + 2 * ∑ k ∈ Icc 1 n, c k ≤ 0) (K : ℕ) (v : Fin K → ℝ) :
    qf (toeplitzLadder c K) v ≤ 0 :=
  qf_nonpos_of_mulVec_nonpos (toeplitzLadder_isSymm c K) (toeplitzLadder_isMetzler hc K)
    (π := fun _ => 1) (fun _ => one_pos) (fun i => by
      simp only [mulVec, dotProduct, toeplitzLadder, Matrix.of_apply, mul_one]
      exact (sum_toeplitz_row_le hc i).trans (hσ K)) v

/-! ### Two far copies -/

/-- **A positive square at one depth gives two at a larger depth** when the couplings decay. -/
theorem not_isHyperbolic_toeplitzLadder {c : ℕ → ℝ} (hdecay : Tendsto c atTop (nhds 0))
    {L : ℕ} {u : Fin L → ℝ} (hu : 0 < qf (toeplitzLadder c L) u) :
    ∃ K, ¬ IsHyperbolic (toeplitzLadder c K) := by
  set q := qf (toeplitzLadder c L) u
  set s := ∑ a, |u a|
  have hs : 0 ≤ s := sum_nonneg fun a _ => abs_nonneg _
  -- far along the ladder the couplings are below `q / (s² + 1)`
  set ε := q / (s ^ 2 + 1)
  have hε : 0 < ε := div_pos hu (by positivity)
  obtain ⟨D, hD⟩ := (Metric.tendsto_atTop.mp hdecay) ε hε
  set K := L + D + L
  -- the two copies
  let U : Fin K → ℝ := fun i => if h : (i : ℕ) < L then u ⟨i, h⟩ else 0
  let V : Fin K → ℝ := fun i => if h : L + D ≤ (i : ℕ) then u ⟨i - (L + D), by omega⟩ else 0
  let e₁ : Fin L → Fin K := fun a => ⟨a, by omega⟩
  let e₂ : Fin L → Fin K := fun a => ⟨a + (L + D), by omega⟩
  have he₁ : Function.Injective e₁ := fun a b h => Fin.ext (by simpa [e₁] using congrArg Fin.val h)
  have he₂ : Function.Injective e₂ := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [e₂] at this; omega)
  have hU : ∀ i, i ∉ Set.range e₁ → U i = 0 := fun i hi => by
    simp only [U]; rw [dif_neg]; intro h; exact hi ⟨⟨i, h⟩, rfl⟩
  have hV : ∀ i, i ∉ Set.range e₂ → V i = 0 := fun i hi => by
    simp only [V]; rw [dif_neg]; intro h; exact hi ⟨⟨i - (L + D), by omega⟩, Fin.ext (by
      simp only [e₂]; omega)⟩
  have hUe : ∀ a, U (e₁ a) = u a := fun a => by simp [U, e₁]
  have hVe : ∀ a, V (e₂ a) = u a := fun a => by
    simp only [V, e₂]; rw [dif_pos (by omega)]; congr 1; ext; simp
  -- each copy has the same positive square
  have hqU : qf (toeplitzLadder c K) U = qf (toeplitzLadder c L) u := by
    rw [qf_eq_sum, qf_eq_sum]
    symm
    refine Fintype.sum_of_injective e₁ he₁ _ _ (fun i hi => by simp [hU i hi]) fun a => ?_
    refine Fintype.sum_of_injective e₁ he₁ _ _ (fun i hi => by simp [hU i hi]) fun b => ?_
    simp only [toeplitzLadder, Matrix.of_apply, hUe, e₁]
  have hqV : qf (toeplitzLadder c K) V = qf (toeplitzLadder c L) u := by
    rw [qf_eq_sum, qf_eq_sum]
    symm
    refine Fintype.sum_of_injective e₂ he₂ _ _ (fun i hi => by simp [hV i hi]) fun a => ?_
    refine Fintype.sum_of_injective e₂ he₂ _ _ (fun i hi => by simp [hV i hi]) fun b => ?_
    simp only [toeplitzLadder, Matrix.of_apply, hVe]
    simp only [e₂, Nat.dist_add_add_right]
  -- and they are almost orthogonal
  have hbil : |bil (toeplitzLadder c K) U V| ≤ s ^ 2 * ε := by
    have e : bil (toeplitzLadder c K) U V =
        ∑ a : Fin L, ∑ b : Fin L, u a * c (Nat.dist (e₁ a) (e₂ b)) * u b := by
      rw [bil_eq_sum]
      symm
      refine Fintype.sum_of_injective e₁ he₁ _ _ (fun i hi => by simp [hU i hi]) fun a => ?_
      refine Fintype.sum_of_injective e₂ he₂ _ _ (fun i hi => by simp [hV i hi]) fun b => ?_
      simp only [toeplitzLadder, Matrix.of_apply, hUe, hVe]
    rw [e]
    calc |∑ a : Fin L, ∑ b : Fin L, u a * c (Nat.dist (e₁ a) (e₂ b)) * u b|
        ≤ ∑ a : Fin L, ∑ b : Fin L, |u a| * ε * |u b| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
          have hlag : D ≤ Nat.dist (e₁ a) (e₂ b) := by
            simp only [e₁, e₂]; unfold Nat.dist; omega
          have hc := hD _ hlag
          rw [Real.dist_eq, sub_zero] at hc
          rw [abs_mul, abs_mul]
          gcongr
      _ = s ^ 2 * ε := by
          simp only [s, sq, sum_mul, mul_sum]
          refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  refine ⟨K, fun hyp => ?_⟩
  have h := hyp U V (by rw [hqU]; exact hu)
  rw [hqU, hqV] at h
  have hlt : s ^ 2 * ε < q := by
    have : s ^ 2 * ε = q * (s ^ 2 / (s ^ 2 + 1)) := by simp only [ε]; field_simp
    rw [this]
    have : s ^ 2 / (s ^ 2 + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    nlinarith
  have hb2 : bil (toeplitzLadder c K) U V ^ 2 < q ^ 2 := by
    have h0 : 0 ≤ s ^ 2 * ε := by positivity
    have := abs_le.mp (hbil.trans hlt.le)
    nlinarith [sq_abs (bil (toeplitzLadder c K) U V), abs_nonneg (bil (toeplitzLadder c K) U V)]
  nlinarith

/-- **An isometric ladder holds its Hodge index only in the stability regime**: for decaying
Metzler couplings it is hyperbolic at every depth iff negative semidefinite at every depth. -/
theorem forall_isHyperbolic_toeplitzLadder_iff {c : ℕ → ℝ} (hdecay : Tendsto c atTop (nhds 0)) :
    (∀ K, IsHyperbolic (toeplitzLadder c K)) ↔
      ∀ K (v : Fin K → ℝ), qf (toeplitzLadder c K) v ≤ 0 := by
  constructor
  · intro h K v
    by_contra hv
    obtain ⟨K', hK'⟩ := not_isHyperbolic_toeplitzLadder hdecay (lt_of_not_ge hv)
    exact hK' (h K')
  · intro h K u v hu
    exact absurd (h K u) (not_le.mpr hu)

/-! ### Conformal ladders -/

/-- A **conformal ladder** `G_{ij} = λ^{min(i,j)} a_{|i−j|}`: the law `G_{i+1,j+1} = λ G_{ij}` of a
Frobenius ladder. -/
def conformalLadder (lam : ℝ) (a : ℕ → ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i j => lam ^ ((min (i : ℕ) j : ℕ) : ℝ) * a (Nat.dist i j)

/-- The normalized couplings `λ^{−k/2} a_k`. -/
def normalizedCoupling (lam : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := lam ^ (-(k : ℝ) / 2) * a k

/-- **A conformal ladder is congruent to the Toeplitz ladder of its normalized couplings.** -/
theorem diagConj_conformalLadder {lam : ℝ} (hlam : 0 < lam) (a : ℕ → ℝ) (K : ℕ) :
    diagConj (fun i : Fin K => lam ^ (-((i : ℕ) : ℝ) / 2)) (conformalLadder lam a K) =
      toeplitzLadder (normalizedCoupling lam a) K := by
  ext i j
  rw [diagConj_apply]
  simp only [conformalLadder, toeplitzLadder, normalizedCoupling, Matrix.of_apply]
  have e : lam ^ (-((i : ℕ) : ℝ) / 2) * (lam ^ ((min (i : ℕ) j : ℕ) : ℝ) * a (Nat.dist i j)) *
      lam ^ (-((j : ℕ) : ℝ) / 2) =
      lam ^ (-((i : ℕ) : ℝ) / 2 + ((min (i : ℕ) j : ℕ) : ℝ) + -((j : ℕ) : ℝ) / 2) *
        a (Nat.dist i j) := by
    rw [Real.rpow_add hlam, Real.rpow_add hlam]; ring
  rw [e]
  congr 2
  rcases le_total (i : ℕ) j with h | h
  · rw [min_eq_left h, show Nat.dist i j = (j : ℕ) - i by unfold Nat.dist; omega,
      Nat.cast_sub h]
    ring
  · rw [min_eq_right h, show Nat.dist i j = (i : ℕ) - j by unfold Nat.dist; omega,
      Nat.cast_sub h]
    ring

/-- **A conformal ladder with decaying normalized couplings holds its Hodge index only in the
stability regime.** -/
theorem forall_isHyperbolic_conformalLadder_iff {lam : ℝ} (hlam : 0 < lam) {a : ℕ → ℝ}
    (hdecay : Tendsto (normalizedCoupling lam a) atTop (nhds 0)) :
    (∀ K, IsHyperbolic (conformalLadder lam a K)) ↔
      ∀ K (v : Fin K → ℝ), qf (conformalLadder lam a K) v ≤ 0 := by
  have hπ : ∀ K (i : Fin K), lam ^ (-((i : ℕ) : ℝ) / 2) ≠ 0 := fun K i =>
    (Real.rpow_pos_of_pos hlam _).ne'
  have hhyp : ∀ K, IsHyperbolic (conformalLadder lam a K) ↔
      IsHyperbolic (toeplitzLadder (normalizedCoupling lam a) K) := fun K => by
    rw [← diagConj_conformalLadder hlam a K, isHyperbolic_diagConj_iff (hπ K)]
  have hqf : ∀ K, (∀ v : Fin K → ℝ, qf (conformalLadder lam a K) v ≤ 0) ↔
      ∀ v : Fin K → ℝ, qf (toeplitzLadder (normalizedCoupling lam a) K) v ≤ 0 := fun K => by
    constructor
    · intro h v
      rw [← diagConj_conformalLadder hlam a K, qf_diagConj]
      exact h _
    · intro h v
      have := h (fun i => (lam ^ (-((i : ℕ) : ℝ) / 2))⁻¹ * v i)
      rw [← diagConj_conformalLadder hlam a K, qf_diagConj] at this
      convert this using 2
      funext i
      field_simp [hπ K i]
  simp_rw [hhyp, hqf]
  exact forall_isHyperbolic_toeplitzLadder_iff hdecay

end GaloisForLFunctions.ArithmeticLorentzianGeometry
