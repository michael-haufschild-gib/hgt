import GaloisForLFunctions.RHTower.SteinhausFinitePrimeWeightedCofactor
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# Full-rank cofactor packets preserving a finite prime prefix

Coherent twist extensions have explicit nonzero weighted means. Their node directions form a
Cauchy basis, so some extension eventually escapes every proper node subspace. Freezing all
coordinates below each selected cutoff preserves earlier vectors and constructs one phase with
a full-rank finite packet above any prescribed cutoff bound.

This is a qualitative cofactor construction. It does not assert a lower bound for a literal
smooth-AFE conditional Gram matrix, a target probability, or recurrence of the vertical flow.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- The literal weighted cofactor prefix, normalized separately at each node. -/
def cofactorNodeVector {J : ℕ} (s : Fin J → ℂ) (N : ℕ)
    (omega : SteinhausModel.Omega) : Fin J → ℂ := fun j =>
  (∑ n ∈ Icc 1 N, SteinhausModel.X n omega * (n : ℂ) ^ (s j - 1)) *
    (N : ℂ) ^ (-s j)

private theorem cauchyMode_span {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) :
    Submodule.span ℂ (Set.range (fun i : Fin J =>
      fun j : Fin J => (s j + (i.val : ℂ) * Complex.I)⁻¹)) = ⊤ := by
  let x : Fin J → ℂ := fun i => (i.val : ℂ) * Complex.I
  have hx : Function.Injective x := by
    intro i k h
    have hh := congrArg Complex.im h
    simp only [x, Complex.mul_im, Complex.natCast_re, Complex.I_im, mul_one,
      Complex.natCast_im, Complex.I_re, mul_zero, add_zero] at hh
    exact Fin.ext (by exact_mod_cast hh)
  have hnonzero : ∀ i j, x i + s j ≠ 0 := by
    intro i j h
    have hh := congrArg Complex.re h
    have hp := hs j
    simp [x] at hh
    linarith
  have hdet : (GaloisForLFunctions.HTGeometry.cauchyMatrix x s).det ≠ 0 := by
    intro h
    have hh := GaloisForLFunctions.HTGeometry.det_cauchyMatrix x s hnonzero
    rw [h, zero_mul] at hh
    have hp : (∏ i, ∏ j ∈ Ioi i, (x i - x j) * (s i - s j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
      exact mul_ne_zero (sub_ne_zero.mpr (fun h => hij (hx h)))
        (sub_ne_zero.mpr (fun h => hij (hinj h)))
    exact hp hh.symm
  have hlin := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hspan := hlin.span_eq_top_of_card_eq_finrank' (by simp)
  change Submodule.span ℂ (Set.range (fun i => fun j => (x i + s j)⁻¹)) = ⊤ at hspan
  simpa only [x, add_comm] using hspan

/-- One coherent extension eventually escapes every prescribed proper node subspace. -/
theorem exists_twist_eventually_cofactorNodeVector_notMem
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega)
    (V : Submodule ℂ (Fin J → ℂ)) (hV : V ≠ ⊤) :
    ∃ t : ℝ, ∀ᶠ N : ℕ in atTop,
      cofactorNodeVector s N (finitePrimeTwistExtension S omega t) ∉ V := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin J,
      (fun j => (s j + (i.val : ℂ) * Complex.I)⁻¹) ∉ V := by
    by_contra! hall
    apply hV
    apply top_unique
    rw [← cauchyMode_span s hs hinj]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  let t : ℝ := i.val
  let A := finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  have houtside : (fun j => A / (s j + (t : ℂ) * Complex.I)) ∉ V := by
    have heq : (fun j => A / (s j + (t : ℂ) * Complex.I)) =
        A • (fun j => (s j + (i.val : ℂ) * Complex.I)⁻¹) := by
      ext j
      simp [t, div_eq_mul_inv]
    rw [heq, V.smul_mem_iff hA]
    exact hi
  have hlim : Tendsto (fun N : ℕ => (N : ℂ) ^ (-((t : ℂ) * Complex.I)) •
        cofactorNodeVector s N (finitePrimeTwistExtension S omega t)) atTop
      (𝓝 (fun j => A / (s j + (t : ℂ) * Complex.I))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply (tendsto_finitePrimeTwistExtension_weighted_mean S omega t (hs j) (hs1 j)).congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [Pi.smul_apply, smul_eq_mul, cofactorNodeVector]
    symm
    calc
      _ = (∑ n ∈ Icc 1 N, SteinhausModel.X n (finitePrimeTwistExtension S omega t) *
          (n : ℂ) ^ (s j - 1)) * ((N : ℂ) ^ (-s j) *
            (N : ℂ) ^ (-((t : ℂ) * Complex.I))) := by ring
      _ = _ := by rw [← Complex.cpow_add _ _ hN0]; congr 2; ring
  have hev := hlim.eventually (V.closed_of_finiteDimensional.isOpen_compl.mem_nhds houtside)
  refine ⟨t, ?_⟩
  filter_upwards [hev] with N hN
  intro hmem
  exact hN (V.smul_mem _ hmem)

/-- Arbitrarily large cofactor vectors escape a proper subspace without changing the prefix. -/
theorem exists_cofactorNodeVector_extension_notMem
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (B : ℕ)
    (V : Submodule ℂ (Fin J → ℂ)) (hV : V ≠ ⊤) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ N : ℕ, B ≤ N ∧ cofactorNodeVector s N omega' ∉ V := by
  obtain ⟨t, ht⟩ := exists_twist_eventually_cofactorNodeVector_notMem s hs hs1 hinj S omega V hV
  obtain ⟨N, hN, hvec⟩ := (eventually_ge_atTop B |>.and ht).exists
  exact ⟨finitePrimeTwistExtension S omega t,
    fun _ hp => finitePrimeTwistExtension_eq_on_prefix S omega t hp, N, hN, hvec⟩

/-- A cofactor prefix reads only the phase coordinates at integers up to its cutoff. -/
theorem cofactorNodeVector_congr_prefix {J : ℕ} (s : Fin J → ℂ) (N : ℕ)
    {omega omega' : SteinhausModel.Omega}
    (hphase : ∀ p ≤ N, omega p = omega' p) :
    cofactorNodeVector s N omega = cofactorNodeVector s N omega' := by
  classical
  ext j
  unfold cofactorNodeVector
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  unfold SteinhausModel.X
  congr 3
  apply Finset.sum_congr rfl
  intro p hp
  rw [hphase p (le_trans (Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; omega)
    (Nat.dvd_of_mem_primeFactors hp)) (mem_Icc.mp hn).2)]

private theorem exists_independent_cofactor_packet_aux
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (B : ℕ) :
    ∀ k : ℕ, k ≤ J → ∃ omega' : SteinhausModel.Omega,
      (∀ p ∈ S, omega' p = omega p) ∧ ∃ M : Fin k → ℕ,
        (∀ i, B ≤ M i) ∧ LinearIndependent ℂ (fun i => cofactorNodeVector s (M i) omega') := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨omega, fun _ _ => rfl, Fin.elim0, fun i => Fin.elim0 i,
      linearIndependent_empty_type⟩
  | succ k ih =>
    intro hk
    obtain ⟨omega₀, hphase₀, M, hM, hlin⟩ := ih (by omega)
    let V := Submodule.span ℂ (Set.range (fun i => cofactorNodeVector s (M i) omega₀))
    have hV : V ≠ ⊤ := by
      intro hv
      have hdim := finrank_span_eq_card hlin
      rw [show Submodule.span ℂ (Set.range (fun i => cofactorNodeVector s (M i) omega₀)) = ⊤
        from hv] at hdim
      simp at hdim
      omega
    let S' := S ∪ Finset.univ.biUnion (fun i => Finset.range (M i + 1))
    obtain ⟨omega₁, hphase₁, N, hN, hout⟩ :=
      exists_cofactorNodeVector_extension_notMem s hs hs1 hinj S' omega₀ B V hV
    have hrows : ∀ i, cofactorNodeVector s (M i) omega₁ =
        cofactorNodeVector s (M i) omega₀ := by
      intro i
      apply cofactorNodeVector_congr_prefix
      intro p hp
      apply hphase₁ p
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩)
    refine ⟨omega₁, ?_, Fin.snoc M N, ?_, ?_⟩
    · intro p hp
      exact (hphase₁ p (Finset.mem_union_left _ hp)).trans (hphase₀ p hp)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hN
      · simpa using hM j
    · have heq : (fun i => cofactorNodeVector s ((Fin.snoc M N : Fin (k + 1) → ℕ) i) omega₁) =
          Fin.snoc (fun i => cofactorNodeVector s (M i) omega₀)
            (cofactorNodeVector s N omega₁) := by
        ext i j
        refine Fin.lastCases ?_ (fun l => ?_) i
        · simp
        · simpa using congrFun (hrows l) j
      rw [heq, linearIndependent_finSnoc]
      exact ⟨hlin, hout⟩

/-- One phase extending any prescribed finite prefix has a full-rank cofactor packet,
with every cofactor cutoff above an arbitrary prescribed bound. -/
theorem exists_fullRank_cofactor_packet
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (B : ℕ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ M : Fin J → ℕ, (∀ i, B ≤ M i) ∧
        (Matrix.of (fun i j => cofactorNodeVector s (M i) omega' j)).det ≠ 0 := by
  obtain ⟨omega', hp, M, hM, hlin⟩ :=
    exists_independent_cofactor_packet_aux s hs hs1 hinj S omega B J le_rfl
  refine ⟨omega', hp, M, hM, ?_⟩
  have hunit : IsUnit (Matrix.of (fun i j => cofactorNodeVector s (M i) omega' j)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hlin
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end RHTower
