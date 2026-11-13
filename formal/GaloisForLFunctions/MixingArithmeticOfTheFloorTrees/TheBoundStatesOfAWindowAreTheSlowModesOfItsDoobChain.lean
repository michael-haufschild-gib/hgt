import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow

/-!
# The bound states of a window are the slow modes of its Doob chain

Let `G` be a real symmetric matrix whose entries off the diagonal are `≤ 0`, and `φ > 0` an
eigenvector, `G φ = λ φ`. Conjugation by `φ` turns `G` into the generator of a reversible chain:
the **Doob chain** with stationary weights `φ_i²` and conductances `c_{ij} = −G_{ij} φ_i φ_j`.

* **Ground-state transform** (`bilin_mul_eq_doob`):
  `G(φf, φf) = λ Σ φ_i² f_i² + ½ Σ_{i,j} c_{ij} (f_i − f_j)²`.
  So `λ` is the least eigenvalue (`lam_mul_sum_sq_le_bilin`), and `μ = −λ` is the **binding
  energy**.
* **Ground vector** (`exists_pos_eigenvector`): if the entries off the diagonal are `< 0`, the
  least eigenvalue has an eigenvector with positive entries. The proof takes an eigenvector of
  the least eigenvalue, replaces it by its modulus, which does not raise the form, and reads
  positivity off the eigenvalue equation.
* **Poincaré form of one bound state** (`hermNegIndex_le_one_iff_poincare`): `G` has at most one
  negative square iff `μ Σ φ_i² f_i² ≤ ½ Σ c_{ij}(f_i − f_j)²` whenever `Σ φ_i² f_i = 0`: the
  spectral gap of the Doob chain is at least the binding energy.
* **Bottlenecks** (`two_le_hermNegIndex_of_bottleneck`): a set `S` whose cut conductance is below
  `μ π(S) π(Sᶜ)/π` gives a second bound state; the test is the centred indicator of `S`.

On windows (`neutralWindow`, whose entries off the diagonal are minus the jets and the floor-map
contacts): every window has a positive ground vector, its binding energy is positive once it
contains a dyadic window, and the Riemann hypothesis holds iff on every window with `R ≤ J` the
Doob chain of the neutral part has spectral gap at least its binding energy
(`riemannHypothesis_iff_forall_doob_poincare`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open scoped RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

section Chain

variable {ι : Type*} [Fintype ι]

/-! ### The Doob chain of a symmetric matrix -/

/-- The conductance between `i` and `j` of the Doob chain of `G` at the vector `φ`. -/
def doobConductance (G : Matrix ι ι ℝ) (φ : ι → ℝ) (i j : ι) : ℝ := -G i j * φ i * φ j

/-- The Dirichlet form of the Doob chain. -/
def doobEnergy (G : Matrix ι ι ℝ) (φ f : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, doobConductance G φ i j * (f i - f j) ^ 2

/-- The integral of `f` against the stationary weights `φ²`. -/
def doobMean (φ f : ι → ℝ) : ℝ := ∑ i, φ i ^ 2 * f i

/-- The second moment of `f` against the stationary weights `φ²`. -/
def doobMass (φ f : ι → ℝ) : ℝ := ∑ i, φ i ^ 2 * f i ^ 2

theorem doobConductance_comm {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i) (φ : ι → ℝ)
    (i j : ι) : doobConductance G φ i j = doobConductance G φ j i := by
  unfold doobConductance
  rw [hG i j]
  ring

theorem doobMass_nonneg (φ f : ι → ℝ) : 0 ≤ doobMass φ f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The Dirichlet form is nonnegative when the entries off the diagonal are `≤ 0`. -/
theorem doobEnergy_nonneg {G : Matrix ι ι ℝ} (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ}
    (hφ : ∀ i, 0 ≤ φ i) (f : ι → ℝ) : 0 ≤ doobEnergy G φ f := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  by_cases hij : i = j
  · rw [hij, sub_self]
    simp
  · refine mul_nonneg ?_ (sq_nonneg _)
    unfold doobConductance
    exact mul_nonneg (mul_nonneg (neg_nonneg.mpr (hoff i j hij)) (hφ i)) (hφ j)

theorem mulVec_eq_smul_apply {G : Matrix ι ι ℝ} {φ : ι → ℝ} {lam : ℝ} (hφ : G *ᵥ φ = lam • φ)
    (i : ι) : ∑ j, G i j * φ j = lam * φ i := by
  have h := congrFun hφ i
  simpa [Matrix.mulVec, dotProduct] using h

/-- **The ground-state transform**: conjugated by an eigenvector `φ`, the form of `G` is the
eigenvalue times the mass plus the Dirichlet form of the Doob chain. -/
theorem bilin_mul_eq_doob {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i) {φ : ι → ℝ}
    {lam : ℝ} (hφ : G *ᵥ φ = lam • φ) (f : ι → ℝ) :
    bilin G (fun i => φ i * f i) (fun i => φ i * f i) =
      lam * doobMass φ f + doobEnergy G φ f := by
  have hA : lam * doobMass φ f = ∑ i, ∑ j, G i j * φ i * φ j * f i ^ 2 := by
    unfold doobMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∑ j, G i j * φ i * φ j * f i ^ 2 = φ i * f i ^ 2 * ∑ j, G i j * φ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h, mulVec_eq_smul_apply hφ i]
    ring
  have hB : lam * doobMass φ f = ∑ i, ∑ j, G i j * φ i * φ j * f j ^ 2 := by
    rw [hA, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hG j i]
      ring
  have h1 : bilin G (fun i => φ i * f i) (fun i => φ i * f i) =
      ∑ i, ∑ j, G i j * φ i * φ j * (f i * f j) := by
    unfold bilin
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : doobEnergy G φ f = ∑ i, ∑ j, ((1 / 2) * (G i j * φ i * φ j * f i ^ 2) +
      (1 / 2) * (G i j * φ i * φ j * f j ^ 2) - G i j * φ i * φ j * (f i * f j)) := by
    unfold doobEnergy doobConductance
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h1]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hA, ← hB]
  ring

/-- **A positive eigenvector belongs to the least eigenvalue**: the form is at least the
eigenvalue times the squared norm. -/
theorem lam_mul_sum_sq_le_bilin {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : G *ᵥ φ = lam • φ) (x : ι → ℝ) :
    lam * ∑ i, x i ^ 2 ≤ bilin G x x := by
  have hx : x = fun i => φ i * (x i / φ i) := funext fun i => by
    field_simp [(hφ i).ne']
  have hmass : doobMass φ (fun i => x i / φ i) = ∑ i, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      field_simp [(hφ i).ne']
  conv_rhs => rw [hx]
  rw [bilin_mul_eq_doob hG heig, hmass]
  linarith [doobEnergy_nonneg hoff (fun i => (hφ i).le) (fun i => x i / φ i)]

/-- A symmetric matrix with nonnegative form kills every vector on which the form vanishes. -/
theorem mulVec_eq_zero_of_dotProduct_eq_zero {M : Matrix ι ι ℝ} (hM : ∀ i j, M i j = M j i)
    (hpos : ∀ σ, 0 ≤ σ ⬝ᵥ (M *ᵥ σ)) {w : ι → ℝ} (hw : w ⬝ᵥ (M *ᵥ w) = 0) : M *ᵥ w = 0 := by
  have hMt : Mᵀ = M := Matrix.ext fun i j => hM j i
  have hsym : ∀ x y : ι → ℝ, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := fun x y => by
    rw [Matrix.dotProduct_mulVec, ← hMt, Matrix.vecMul_transpose, hMt, dotProduct_comm]
  have hexp : ∀ t : ℝ, (w + t • (M *ᵥ w)) ⬝ᵥ (M *ᵥ (w + t • (M *ᵥ w))) =
      2 * t * ((M *ᵥ w) ⬝ᵥ (M *ᵥ w)) + t ^ 2 * ((M *ᵥ w) ⬝ᵥ (M *ᵥ (M *ᵥ w))) := by
    intro t
    have hwz : w ⬝ᵥ (M *ᵥ (M *ᵥ w)) = (M *ᵥ w) ⬝ᵥ (M *ᵥ w) := hsym _ _
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hw, hwz]
    ring
  have hq0 : 0 ≤ (M *ᵥ w) ⬝ᵥ (M *ᵥ (M *ᵥ w)) := hpos _
  generalize hS : (M *ᵥ w) ⬝ᵥ (M *ᵥ w) = S at hexp
  generalize hq : (M *ᵥ w) ⬝ᵥ (M *ᵥ (M *ᵥ w)) = q at hexp hq0
  have hq1 : 0 < q + 1 := by linarith
  have h0 := hpos (w + (-S / (q + 1)) • (M *ᵥ w))
  rw [hexp] at h0
  have e : (q + 1) ^ 2 * (2 * (-S / (q + 1)) * S + (-S / (q + 1)) ^ 2 * q) =
      -(S ^ 2 * (q + 2)) := by
    field_simp
    ring
  have hle : 0 ≤ -(S ^ 2 * (q + 2)) := e ▸ mul_nonneg (sq_nonneg _) h0
  have hS0 : S = 0 := by nlinarith [sq_nonneg S]
  exact Matrix.dotProduct_self_eq_zero.mp (hS.trans hS0)

/-- Against a matrix with entries `≤ 0` off the diagonal the modulus does not raise the form. -/
theorem bilin_abs_le {G : Matrix ι ι ℝ} (hoff : ∀ i j, i ≠ j → G i j ≤ 0) (v : ι → ℝ) :
    bilin G (fun i => |v i|) (fun i => |v i|) ≤ bilin G v v := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i = j
  · rw [hij, abs_mul_abs_self]
  · have h1 : v i * v j ≤ |v i| * |v j| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith [hoff i j hij]

/-- **The ground vector.** If the entries off the diagonal are negative, some eigenvector of the
least eigenvalue has positive entries. -/
theorem exists_pos_eigenvector [DecidableEq ι] [Nonempty ι] {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j < 0) :
    ∃ φ : ι → ℝ, (∀ i, 0 < φ i) ∧ ∃ lam : ℝ, G *ᵥ φ = lam • φ := by
  have hB : G.IsHermitian := isHermitian_of_symm hG
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ hB.eigenvalues Finset.univ_nonempty
  set lam := hB.eigenvalues i₀
  set v : ι → ℝ := fun k => hB.eigenvectorBasis i₀ k
  -- the Rayleigh bound by the least eigenvalue
  have hparseval : ∀ σ : ι → ℝ,
      ∑ i, (∑ k, σ k * hB.eigenvectorBasis i k) ^ 2 = ∑ k, σ k ^ 2 := by
    intro σ
    have h := hB.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 σ) (WithLp.toLp 2 σ)
    have h' : ∀ i, ⟪hB.eigenvectorBasis i, (WithLp.toLp 2 σ : EuclideanSpace ℝ ι)⟫ =
        ∑ k, σ k * hB.eigenvectorBasis i k := fun i => by
      rw [real_inner_comm]
      exact inner_toLp_eigenvector hB σ i
    have hself : ⟪(WithLp.toLp 2 σ : EuclideanSpace ℝ ι), WithLp.toLp 2 σ⟫ = ∑ k, σ k ^ 2 := by
      simp [PiLp.inner_apply, sq]
    simp only [inner_toLp_eigenvector hB, h', hself] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => sq _
  have hray : ∀ σ : ι → ℝ, lam * ∑ k, σ k ^ 2 ≤ σ ⬝ᵥ (G *ᵥ σ) := by
    intro σ
    rw [dotProduct_mulVec_eq_sum_eigen hB, ← hparseval, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi₀ i (Finset.mem_univ i))
      (sq_nonneg _)
  have hv : G *ᵥ v = lam • v := hB.mulVec_eigenvectorBasis i₀
  have hvv : ∑ k, v k * v k = 1 := (eigenvector_orthonormal hB i₀ i₀).trans (if_pos rfl)
  set w : ι → ℝ := fun k => |v k|
  have hww : ∑ k, w k ^ 2 = 1 := by
    rw [← hvv]
    exact Finset.sum_congr rfl fun k _ => by simp only [w, sq_abs, sq]
  -- the modulus is a minimizer, hence an eigenvector
  have hform : w ⬝ᵥ (G *ᵥ w) = lam * ∑ k, w k ^ 2 := by
    refine le_antisymm ?_ (hray w)
    rw [dotProduct_mulVec_eq_bilin, hww]
    calc bilin G w w ≤ bilin G v v := bilin_abs_le (fun i j h => (hoff i j h).le) v
      _ = lam := by rw [bilin_eigen hv, hvv, mul_one]
      _ = lam * 1 := (mul_one _).symm
  set M : Matrix ι ι ℝ := G - lam • (1 : Matrix ι ι ℝ)
  have hMv : ∀ σ : ι → ℝ, σ ⬝ᵥ (M *ᵥ σ) = σ ⬝ᵥ (G *ᵥ σ) - lam * ∑ k, σ k ^ 2 := by
    intro σ
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    rw [show σ ⬝ᵥ σ = ∑ k, σ k ^ 2 from Finset.sum_congr rfl fun k _ => (sq _).symm]
  have hMsym : ∀ i j, M i j = M j i := fun i j => by
    by_cases h : i = j
    · rw [h]
    · simp [M, Matrix.one_apply, h, Ne.symm h, hG i j]
  have hMw : M *ᵥ w = 0 := mulVec_eq_zero_of_dotProduct_eq_zero hMsym
    (fun σ => by rw [hMv]; linarith [hray σ]) (by rw [hMv, hform]; ring)
  have hGw : G *ᵥ w = lam • w := by
    have h := hMw
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h
  -- positivity from the eigenvalue equation
  refine ⟨w, fun i => ?_, lam, hGw⟩
  rcases (abs_nonneg (v i)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hrow := mulVec_eq_smul_apply hGw i
    rw [show w i = 0 from h.symm, mul_zero] at hrow
    have hterm : ∀ j ∈ Finset.univ, G i j * w j ≤ 0 := fun j _ => by
      by_cases hij : i = j
      · rw [← hij, show w i = 0 from h.symm, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff i j hij).le (abs_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hrow
    have hw0 : ∀ j, w j = 0 := fun j => by
      by_cases hij : i = j
      · rw [← hij]
        exact h.symm
      · exact (mul_eq_zero.mp (hzero j (Finset.mem_univ j))).resolve_left (hoff i j hij).ne
    have : ∑ k, w k ^ 2 = 0 := Finset.sum_eq_zero fun k _ => by rw [hw0 k]; ring
    linarith

/-! ### One bound state as a Poincaré inequality -/

/-- **One bound state is the Poincaré inequality of the Doob chain with the binding energy as
constant.** -/
theorem hermNegIndex_le_one_iff_poincare {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : G *ᵥ φ = lam • φ) :
    hermNegIndex (G.map (↑) : Matrix ι ι ℂ) ≤ 1 ↔
      ∀ f : ι → ℝ, doobMean φ f = 0 → -lam * doobMass φ f ≤ doobEnergy G φ f := by
  constructor
  · intro h f hf
    by_contra hlt
    rw [not_le] at hlt
    set x : ι → ℝ := fun i => φ i * f i
    have hE := doobEnergy_nonneg hoff (fun i => (hφ i).le) f
    have hxx : bilin G x x < 0 := by
      rw [bilin_mul_eq_doob hG heig]
      linarith
    have hmass : 0 < doobMass φ f := by
      rcases (doobMass_nonneg φ f).lt_or_eq with hm | hm
      · exact hm
      · rw [← hm] at hlt
        linarith
    have hlam : lam < 0 := by
      by_contra hl
      have : 0 ≤ lam * doobMass φ f := mul_nonneg (not_lt.mp hl) hmass.le
      rw [bilin_mul_eq_doob hG heig] at hxx
      linarith
    have hne : (Finset.univ : Finset ι).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [doobMass, hne] at hmass
    have hφφ : bilin G φ φ < 0 := by
      rw [bilin_eigen heig]
      exact mul_neg_of_neg_of_pos hlam (Finset.sum_pos (fun i _ => mul_pos (hφ i) (hφ i)) hne)
    have hφx : bilin G φ x = 0 := by
      rw [bilin_swap hG, bilin_eigen heig]
      have : ∑ k, x k * φ k = doobMean φ f :=
        Finset.sum_congr rfl fun k _ => by simp only [x]; ring
      rw [this, hf, mul_zero]
    have h2 := two_le_hermNegIndex_of_unbound_pair hG hφφ
      (by rw [hφx]; nlinarith [mul_pos_of_neg_of_neg hφφ hxx])
    omega
  · intro h
    refine (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
      (G.map (↑) : Matrix ι ι ℂ) (fun _ : Unit => realChargeForm φ) fun z hz => ?_).trans
      (le_of_eq Fintype.card_unit)
    have key : ∀ y : ι → ℝ, ∑ i, φ i * y i = 0 → 0 ≤ y ⬝ᵥ (G *ᵥ y) := by
      intro y hy
      have hyf : y = fun i => φ i * (y i / φ i) := funext fun i => by
        field_simp [(hφ i).ne']
      have hmean : doobMean φ (fun i => y i / φ i) = 0 := by
        rw [← hy]
        exact Finset.sum_congr rfl fun i _ => by field_simp [(hφ i).ne']
      rw [dotProduct_mulVec_eq_bilin, hyf, bilin_mul_eq_doob hG heig]
      linarith [h _ hmean]
    have hc : ∑ m, ((φ m : ℝ) : ℂ) * z m = 0 := hz ()
    rw [HeckeKreinToeplitz.hermQuad_map_ofReal]
    refine add_nonneg (key _ ?_) (key _ ?_)
    · have h1 := congrArg Complex.re hc
      rw [Complex.re_sum, Complex.zero_re] at h1
      exact (Finset.sum_congr rfl fun m _ => (Complex.re_ofReal_mul _ _).symm).trans h1
    · have h1 := congrArg Complex.im hc
      rw [Complex.im_sum, Complex.zero_im] at h1
      exact (Finset.sum_congr rfl fun m _ => (Complex.im_ofReal_mul _ _).symm).trans h1

/-! ### Bottlenecks -/

variable [DecidableEq ι]

/-- The stationary weight of a set of indices. -/
def doobWeight (φ : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, φ i ^ 2

/-- The conductance of the cut between `S` and its complement. -/
def doobCut (G : Matrix ι ι ℝ) (φ : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, doobConductance G φ i j

/-- A double sum restricted to a product of two sets. -/
theorem sum_sum_ite_and (S T : Finset ι) (c : ι → ι → ℝ) :
    ∑ i, ∑ j, (if i ∈ S ∧ j ∈ T then c i j else 0) = ∑ i ∈ S, ∑ j ∈ T, c i j := by
  calc ∑ i, ∑ j, (if i ∈ S ∧ j ∈ T then c i j else 0)
      = ∑ i, (if i ∈ S then ∑ j, (if j ∈ T then c i j else 0) else 0) :=
        Finset.sum_congr rfl fun i _ => by by_cases hi : i ∈ S <;> simp [hi]
    _ = ∑ i ∈ S, ∑ j, (if j ∈ T then c i j else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i ∈ S, ∑ j ∈ T, c i j :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The Dirichlet form of a shifted indicator is the conductance of its cut. -/
theorem doobEnergy_indicator_sub {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i) (φ : ι → ℝ)
    (S : Finset ι) (c : ℝ) :
    doobEnergy G φ (fun i => (if i ∈ S then 1 else 0) - c) = doobCut G φ S := by
  have hsq : ∀ i j, ((if i ∈ S then (1 : ℝ) else 0) - c - ((if j ∈ S then 1 else 0) - c)) ^ 2 =
      (if i ∈ S ∧ j ∈ Sᶜ then 1 else 0) + (if i ∈ Sᶜ ∧ j ∈ S then 1 else 0) := by
    intro i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
  have hsplit : ∀ i j, doobConductance G φ i j *
      ((if i ∈ S then (1 : ℝ) else 0) - c - ((if j ∈ S then 1 else 0) - c)) ^ 2 =
      (if i ∈ S ∧ j ∈ Sᶜ then doobConductance G φ i j else 0) +
        (if i ∈ Sᶜ ∧ j ∈ S then doobConductance G φ i j else 0) := by
    intro i j
    rw [hsq, mul_add, mul_ite, mul_ite, mul_one, mul_zero, mul_one, mul_zero]
  have hswap : ∑ i ∈ Sᶜ, ∑ j ∈ S, doobConductance G φ i j = doobCut G φ S := by
    unfold doobCut
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      doobConductance_comm hG φ j i
  unfold doobEnergy
  simp only [hsplit, Finset.sum_add_distrib, sum_sum_ite_and, hswap]
  unfold doobCut
  ring

/-- **A bottleneck below the binding energy gives a second bound state**: if the cut of `S` has
conductance below `μ π(S) π(Sᶜ)/π`, with `μ = −λ` and `π` the stationary weights, the form has two
negative squares. -/
theorem two_le_hermNegIndex_of_bottleneck {G : Matrix ι ι ℝ} (hG : ∀ i j, G i j = G j i)
    (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : G *ᵥ φ = lam • φ) (S : Finset ι)
    (hcut : doobCut G φ S * doobWeight φ Finset.univ <
      -lam * doobWeight φ S * doobWeight φ Sᶜ) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  by_contra hlt
  have hP := (hermNegIndex_le_one_iff_poincare hG hoff hφ heig).mp (by omega)
  have hW : doobWeight φ Finset.univ = doobWeight φ S + doobWeight φ Sᶜ :=
    (Finset.sum_add_sum_compl S _).symm
  have hSnn : 0 ≤ doobWeight φ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hScnn : 0 ≤ doobWeight φ Sᶜ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hWpos : 0 < doobWeight φ Finset.univ := by
    by_contra hW0
    have h0 : doobWeight φ Finset.univ = 0 := le_antisymm (not_lt.mp hW0)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hS0 : doobWeight φ S = 0 := by linarith
    have hcut0 : doobCut G φ S * doobWeight φ Finset.univ = 0 := by rw [h0, mul_zero]
    rw [hcut0, hS0, mul_zero, zero_mul] at hcut
    exact lt_irrefl _ hcut
  set c := doobWeight φ S / doobWeight φ Finset.univ
  set f : ι → ℝ := fun i => (if i ∈ S then 1 else 0) - c
  have hsum : ∀ g : ι → ℝ, ∑ i, φ i ^ 2 * g i =
      ∑ i ∈ S, φ i ^ 2 * g i + ∑ i ∈ Sᶜ, φ i ^ 2 * g i := fun g =>
    (Finset.sum_add_sum_compl S _).symm
  have hmean : doobMean φ f = 0 := by
    unfold doobMean
    rw [hsum]
    have h1 : ∑ i ∈ S, φ i ^ 2 * f i = (1 - c) * doobWeight φ S := by
      rw [doobWeight, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by simp only [f, if_pos hi]; ring
    have h2 : ∑ i ∈ Sᶜ, φ i ^ 2 * f i = -c * doobWeight φ Sᶜ := by
      rw [doobWeight, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        simp only [f, if_neg (Finset.mem_compl.mp hi)]
        ring
    rw [h1, h2]
    simp only [c]
    rw [hW] at hWpos ⊢
    field_simp
    ring
  have hmass : doobMass φ f * doobWeight φ Finset.univ =
      doobWeight φ S * doobWeight φ Sᶜ := by
    unfold doobMass
    have hsum2 : ∑ i, φ i ^ 2 * f i ^ 2 =
        ∑ i ∈ S, φ i ^ 2 * f i ^ 2 + ∑ i ∈ Sᶜ, φ i ^ 2 * f i ^ 2 :=
      (Finset.sum_add_sum_compl S _).symm
    have h1 : ∑ i ∈ S, φ i ^ 2 * f i ^ 2 = (1 - c) ^ 2 * doobWeight φ S := by
      rw [doobWeight, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by simp only [f, if_pos hi]; ring
    have h2 : ∑ i ∈ Sᶜ, φ i ^ 2 * f i ^ 2 = c ^ 2 * doobWeight φ Sᶜ := by
      rw [doobWeight, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        simp only [f, if_neg (Finset.mem_compl.mp hi)]
        ring
    rw [hsum2, h1, h2]
    simp only [c]
    rw [hW] at hWpos ⊢
    field_simp
    ring
  have hE : doobEnergy G φ f = doobCut G φ S := doobEnergy_indicator_sub hG φ S c
  have hineq := hP f hmean
  rw [hE] at hineq
  have h3 : -lam * doobMass φ f * doobWeight φ Finset.univ ≤
      doobCut G φ S * doobWeight φ Finset.univ :=
    mul_le_mul_of_nonneg_right hineq hWpos.le
  rw [mul_assoc, hmass] at h3
  linarith

end Chain

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
