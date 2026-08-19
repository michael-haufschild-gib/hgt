import GaloisForLFunctions.HTGeometry.UniversalPrimeKreinHamming

/-!
# Relative Pick defects of prime-residue chambers

The Nevanlinna difference kernel of a finite prime-residue chamber differs from that of any other
chamber by a finite signed sum of rank-one Cauchy features supported on the two directed set
differences.  Sampling the defect on the canonical unit-height probe packet produces exactly the
rectangular Krein form whose inertia is already known, so the relative Pick signature of an
ordered chamber pair is `(#(L \ J), #(J \ L), 0)` and its rank is the Hamming distance.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped BigOperators

noncomputable section

/-- The Nevanlinna--Pick difference kernel of a function. -/
def pickKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (f z - starRingEnd ℂ (f w)) / (z - starRingEnd ℂ w)

/-- The Cauchy atom attached to a real pole. -/
def cauchyAtom (lam : ℝ) (z : ℂ) : ℂ := ((lam : ℂ) - z)⁻¹

theorem pickKernel_sub (f g : ℂ → ℂ) (z w : ℂ) :
    pickKernel (fun ζ => f ζ - g ζ) z w = pickKernel f z w - pickKernel g z w := by
  unfold pickKernel
  rw [← sub_div, map_sub]
  congr 1
  ring

theorem pickKernel_real_smul (r : ℝ) (f : ℂ → ℂ) (z w : ℂ) :
    pickKernel (fun ζ => (r : ℂ) * f ζ) z w = (r : ℂ) * pickKernel f z w := by
  simp only [pickKernel]
  rw [← mul_div_assoc]
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  ring

theorem pickKernel_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z w : ℂ) :
    pickKernel (fun ζ => ∑ i ∈ s, F i ζ) z w = ∑ i ∈ s, pickKernel (F i) z w := by
  simp only [pickKernel]
  rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- **One-atom Pick identity.**  The Pick kernel of a Cauchy atom with a real pole is the rank-one
outer product of that atom. -/
theorem pickKernel_cauchyAtom (lam : ℝ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzw : z ≠ starRingEnd ℂ w) :
    pickKernel (cauchyAtom lam) z w =
      cauchyAtom lam z * starRingEnd ℂ (cauchyAtom lam w) := by
  have ha : ((lam : ℂ) - z) ≠ 0 := by
    intro h
    exact hz (by simpa using congrArg Complex.im (sub_eq_zero.mp h).symm)
  have hb : ((lam : ℂ) - starRingEnd ℂ w) ≠ 0 := by
    intro h
    have := congrArg Complex.im (sub_eq_zero.mp h).symm
    simp only [Complex.conj_im, Complex.ofReal_im] at this
    exact hw (neg_eq_zero.mp this)
  have hd : ((lam : ℂ) - starRingEnd ℂ w) - ((lam : ℂ) - z) ≠ 0 := by
    have : ((lam : ℂ) - starRingEnd ℂ w) - ((lam : ℂ) - z) = z - starRingEnd ℂ w := by ring
    rw [this]
    exact sub_ne_zero.mpr hzw
  have hconj : starRingEnd ℂ (cauchyAtom lam w) = ((lam : ℂ) - starRingEnd ℂ w)⁻¹ := by
    simp [cauchyAtom, map_inv₀, map_sub, Complex.conj_ofReal]
  have hden : z - starRingEnd ℂ w
      = ((lam : ℂ) - starRingEnd ℂ w) - ((lam : ℂ) - z) := by ring
  rw [pickKernel, hconj, hden, cauchyAtom]
  field_simp

/-- The Pick kernel of a finite real-weighted Cauchy divisor. -/
theorem pickKernel_atomCombination {ι : Type*} (s : Finset ι) (c : ι → ℝ) (lam : ι → ℝ)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (hzw : z ≠ starRingEnd ℂ w) :
    pickKernel (fun ζ => ∑ i ∈ s, (c i : ℂ) * cauchyAtom (lam i) ζ) z w =
      ∑ i ∈ s, (c i : ℂ) *
        (cauchyAtom (lam i) z * starRingEnd ℂ (cauchyAtom (lam i) w)) := by
  rw [pickKernel_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pickKernel_real_smul, pickKernel_cauchyAtom (lam i) hz hw hzw]

/-! ## The relative chamber divisor -/

theorem sum_sub_sum_eq_sum_sdiff_sub_sum_sdiff {ι M : Type*} [DecidableEq ι] [AddCommGroup M]
    (J L : Finset ι) (f : ι → M) :
    ∑ p ∈ L, f p - ∑ p ∈ J, f p = ∑ p ∈ L \ J, f p - ∑ p ∈ J \ L, f p := by
  have h1 : ∑ p ∈ L \ J, f p + ∑ p ∈ L ∩ J, f p = ∑ p ∈ L, f p := by
    have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := L) (s₂ := J))
    rwa [Finset.sdiff_inter_self_left] at h
  have h2 : ∑ p ∈ J \ L, f p + ∑ p ∈ J ∩ L, f p = ∑ p ∈ J, f p := by
    have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := J) (s₂ := L))
    rwa [Finset.sdiff_inter_self_left] at h
  have h3 : ∑ p ∈ J ∩ L, f p = ∑ p ∈ L ∩ J, f p := by rw [Finset.inter_comm]
  rw [← h1, ← h2, h3]
  abel

/-- The ordered chamber pair differs by the finite signed Cauchy divisor supported on the two
directed set differences. -/
theorem universalPrimeOrientedHerglotz_sub (J L : Finset Nat.Primes) (z : ℂ) :
    universalPrimeOrientedHerglotz J z - universalPrimeOrientedHerglotz L z =
      (∑ p ∈ L \ J, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          cauchyAtom (primeLogSupport p) z) -
        ∑ p ∈ J \ L, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          cauchyAtom (primeLogSupport p) z := by
  have hbase : ∀ S : Finset Nat.Primes,
      ∑ p ∈ S, ((2 * universalPrimeWeight p : ℝ) : ℂ) * cauchyAtom (primeLogSupport p) z
        = 2 * ∑ p ∈ S, (universalPrimeWeight p : ℂ) *
            ((primeLogSupport p : ℂ) - z)⁻¹ := by
    intro S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast [cauchyAtom]
    ring
  rw [hbase, hbase, universalPrimeOrientedHerglotz, universalPrimeOrientedHerglotz]
  have := sum_sub_sum_eq_sum_sdiff_sub_sum_sdiff (M := ℂ) J L
    (fun p => (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹)
  have h2 : (2 : ℂ) * ∑ p ∈ L, (universalPrimeWeight p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹ -
      2 * ∑ p ∈ J, (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹
      = 2 * (∑ p ∈ L \ J, (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹ -
        ∑ p ∈ J \ L, (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹) := by
    rw [← this]; ring
  linear_combination h2

/-- **Relative Pick defect.**  The difference of the Pick kernels of two finite prime-residue
chambers is a finite signed sum of rank-one Cauchy features:  positive on `L \ J`, negative on
`J \ L`.  The infinitely many common source atoms cancel exactly. -/
theorem pickKernel_universalPrimeOrientedHerglotz_sub (J L : Finset Nat.Primes)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (hzw : z ≠ starRingEnd ℂ w) :
    pickKernel (universalPrimeOrientedHerglotz J) z w -
        pickKernel (universalPrimeOrientedHerglotz L) z w =
      (∑ p ∈ L \ J, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          (cauchyAtom (primeLogSupport p) z *
            starRingEnd ℂ (cauchyAtom (primeLogSupport p) w))) -
        ∑ p ∈ J \ L, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          (cauchyAtom (primeLogSupport p) z *
            starRingEnd ℂ (cauchyAtom (primeLogSupport p) w)) := by
  have hfun : (fun ζ => universalPrimeOrientedHerglotz J ζ -
      universalPrimeOrientedHerglotz L ζ) =
      fun ζ => (∑ p ∈ L \ J, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          cauchyAtom (primeLogSupport p) ζ) -
        ∑ p ∈ J \ L, ((2 * universalPrimeWeight p : ℝ) : ℂ) *
          cauchyAtom (primeLogSupport p) ζ := by
    funext ζ
    exact universalPrimeOrientedHerglotz_sub J L ζ
  have hsplit := pickKernel_sub (universalPrimeOrientedHerglotz J)
    (universalPrimeOrientedHerglotz L) z w
  rw [← hsplit, hfun, pickKernel_sub, pickKernel_atomCombination _ _ _ hz hw hzw,
    pickKernel_atomCombination _ _ _ hz hw hzw]

/-! ## The relative defect Gram on the canonical probe packet -/

theorem primeKreinProbeNode_im (N : ℕ) (j : Fin N) :
    (primeKreinProbeNode N j).im = 1 := by
  simp [primeKreinProbeNode]

theorem primeKreinProbeNode_ne_conj (N : ℕ) (a b : Fin N) :
    primeKreinProbeNode N a ≠ starRingEnd ℂ (primeKreinProbeNode N b) := by
  intro h
  have him := congrArg Complex.im h
  rw [primeKreinProbeNode_im, Complex.conj_im, primeKreinProbeNode_im] at him
  norm_num at him

theorem sum_finsetPrimeEnumeration {M : Type*} [AddCommMonoid M]
    (S : Finset Nat.Primes) (f : Nat.Primes → M) :
    ∑ i : Fin S.card, f (finsetPrimeEnumeration S i) = ∑ p ∈ S, f p := by
  rw [← Finset.sum_coe_sort S f]
  exact Equiv.sum_comp S.equivFin.symm (fun x : S => f (x : Nat.Primes))

/-- The Gram matrix of the relative Pick defect of an ordered chamber pair on the canonical
unit-height probe packet. -/
def universalPrimeChamberRelativePickGram (J L : Finset Nat.Primes) :
    Matrix (Fin ((L \ J).card + (J \ L).card)) (Fin ((L \ J).card + (J \ L).card)) ℂ :=
  Matrix.of fun a b =>
    pickKernel (universalPrimeOrientedHerglotz J)
        (primeKreinProbeNode ((L \ J).card + (J \ L).card) a)
        (primeKreinProbeNode ((L \ J).card + (J \ L).card) b) -
      pickKernel (universalPrimeOrientedHerglotz L)
        (primeKreinProbeNode ((L \ J).card + (J \ L).card) a)
        (primeKreinProbeNode ((L \ J).card + (J \ L).card) b)

/-- **The relative Pick defect is the rectangular Krein form.**  Sampling the Pick defect of an
ordered chamber pair on the canonical probes reproduces exactly the signed Cauchy response Gram
whose inertia is the directed Hamming geometry. -/
theorem universalPrimeChamberRelativePickGram_eq (J L : Finset Nat.Primes) :
    universalPrimeChamberRelativePickGram J L =
      universalPrimeChamberRelativeKreinProbeForm J L := by
  classical
  ext a b
  have hz : (primeKreinProbeNode ((L \ J).card + (J \ L).card) a).im ≠ 0 := by
    rw [primeKreinProbeNode_im]; norm_num
  have hw : (primeKreinProbeNode ((L \ J).card + (J \ L).card) b).im ≠ 0 := by
    rw [primeKreinProbeNode_im]; norm_num
  have hzw := primeKreinProbeNode_ne_conj ((L \ J).card + (J \ L).card) a b
  have hfeature : ∀ (S : Finset Nat.Primes) (i : Fin S.card),
      universalPrimeKreinFeature (finsetPrimeEnumeration S)
          (primeKreinProbeNode ((L \ J).card + (J \ L).card)) i a *
        star (universalPrimeKreinFeature (finsetPrimeEnumeration S)
          (primeKreinProbeNode ((L \ J).card + (J \ L).card)) i b) =
        ((2 * universalPrimeWeight (finsetPrimeEnumeration S i) : ℝ) : ℂ) *
          (cauchyAtom (primeLogSupport (finsetPrimeEnumeration S i))
              (primeKreinProbeNode ((L \ J).card + (J \ L).card) a) *
            starRingEnd ℂ (cauchyAtom (primeLogSupport (finsetPrimeEnumeration S i))
              (primeKreinProbeNode ((L \ J).card + (J \ L).card) b))) := by
    intro S i
    have hnn : (0 : ℝ) ≤ 2 * universalPrimeWeight (finsetPrimeEnumeration S i) :=
      (mul_pos (by norm_num) (universalPrimeWeight_pos _)).le
    have hsq : ((Real.sqrt (2 * universalPrimeWeight (finsetPrimeEnumeration S i)) : ℝ) : ℂ) *
        ((Real.sqrt (2 * universalPrimeWeight (finsetPrimeEnumeration S i)) : ℝ) : ℂ)
        = ((2 * universalPrimeWeight (finsetPrimeEnumeration S i) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
    simp only [universalPrimeKreinFeature, Pi.smul_apply, smul_eq_mul, cauchyAtom,
      star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← hsq]
    ring
  rw [universalPrimeChamberRelativePickGram, Matrix.of_apply,
    pickKernel_universalPrimeOrientedHerglotz_sub J L hz hw hzw,
    universalPrimeChamberRelativeKreinProbeForm, universalPrimeKreinProbeForm,
    rectangularKreinForm]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun i _ => hfeature (L \ J) i),
    Finset.sum_congr rfl (fun i _ => hfeature (J \ L) i)]
  congr 1
  · exact (sum_finsetPrimeEnumeration (L \ J) _).symm
  · exact (sum_finsetPrimeEnumeration (J \ L) _).symm

/-! ## Nondegeneracy and rank -/

/-- The signature pattern of an ordered feature packet. -/
def chamberSignDiagonal (kp kn : ℕ) : Fin (kp + kn) → ℂ := fun i =>
  Sum.elim (fun _ : Fin kp => (1 : ℂ)) (fun _ : Fin kn => (-1 : ℂ)) (finSumFinEquiv.symm i)

theorem chamberSignDiagonal_ne_zero (kp kn : ℕ) (i : Fin (kp + kn)) :
    chamberSignDiagonal kp kn i ≠ 0 := by
  rcases h : finSumFinEquiv.symm i with j | j <;>
    simp [chamberSignDiagonal, h]

/-- The square feature matrix of an ordered packet: its columns are the positive channels
followed by the negative channels. -/
def featurePacketMatrix {kp kn : ℕ}
    (w : Fin kp → (Fin (kp + kn) → ℂ)) (u : Fin kn → (Fin (kp + kn) → ℂ)) :
    Matrix (Fin (kp + kn)) (Fin (kp + kn)) ℂ :=
  Matrix.of fun a i => Sum.elim w u (finSumFinEquiv.symm i) a

/-- **Signature congruence.**  A rectangular Krein form on a square packet is the congruence of the
diagonal signature matrix by the feature matrix. -/
theorem rectangularKreinForm_eq_featureCongruence {kp kn : ℕ}
    (w : Fin kp → (Fin (kp + kn) → ℂ)) (u : Fin kn → (Fin (kp + kn) → ℂ)) :
    rectangularKreinForm w u =
      featurePacketMatrix w u * Matrix.diagonal (chamberSignDiagonal kp kn) *
        (featurePacketMatrix w u)ᴴ := by
  classical
  ext a b
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hdiag : ∀ i : Fin (kp + kn),
      (Matrix.diagonal (chamberSignDiagonal kp kn) * (featurePacketMatrix w u)ᴴ) i b
        = chamberSignDiagonal kp kn i * star (featurePacketMatrix w u b i) := by
    intro i
    rw [Matrix.diagonal_mul]
    simp [Matrix.conjTranspose_apply]
  simp only [hdiag]
  rw [← Equiv.sum_comp (finSumFinEquiv (m := kp) (n := kn))
    (fun i => featurePacketMatrix w u a i *
      (chamberSignDiagonal kp kn i * star (featurePacketMatrix w u b i)))]
  rw [Fintype.sum_sum_type]
  simp only [rectangularKreinForm, Matrix.sub_apply, Matrix.sum_apply, Matrix.of_apply,
    featurePacketMatrix, chamberSignDiagonal, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
    one_mul, neg_mul, mul_neg]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- The relative chamber feature matrix on the canonical probe packet. -/
def universalPrimeChamberFeatureMatrix (J L : Finset Nat.Primes) :
    Matrix (Fin ((L \ J).card + (J \ L).card)) (Fin ((L \ J).card + (J \ L).card)) ℂ :=
  featurePacketMatrix
    (universalPrimeKreinFeature (finsetPrimeEnumeration (L \ J))
      (primeKreinProbeNode ((L \ J).card + (J \ L).card)))
    (universalPrimeKreinFeature (finsetPrimeEnumeration (J \ L))
      (primeKreinProbeNode ((L \ J).card + (J \ L).card)))

theorem isUnit_universalPrimeChamberFeatureMatrix (J L : Finset Nat.Primes) :
    IsUnit (universalPrimeChamberFeatureMatrix J L) := by
  classical
  have hlinear := universalPrimeKreinProbe_combined_linearIndependent
    (finsetPrimeEnumeration (L \ J)) (finsetPrimeEnumeration (J \ L))
    (primeChamberDifferenceEnumeration_injective J L)
  have hcomp := hlinear.comp _
    (finSumFinEquiv (m := (L \ J).card) (n := (J \ L).card)).symm.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp hcomp

/-- **The relative Pick defect is nondegenerate.**  Its null index vanishes, so the Krein signature
of an ordered chamber pair is exactly `(#(L \ J), #(J \ L), 0)`. -/
theorem isUnit_det_universalPrimeChamberRelativePickGram (J L : Finset Nat.Primes) :
    IsUnit (universalPrimeChamberRelativePickGram J L).det := by
  classical
  rw [universalPrimeChamberRelativePickGram_eq, universalPrimeChamberRelativeKreinProbeForm,
    universalPrimeKreinProbeForm, rectangularKreinForm_eq_featureCongruence]
  have hM : IsUnit (universalPrimeChamberFeatureMatrix J L) :=
    isUnit_universalPrimeChamberFeatureMatrix J L
  have hMdet : IsUnit (universalPrimeChamberFeatureMatrix J L).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hM
  have hdiag : IsUnit (Matrix.diagonal (chamberSignDiagonal
      (L \ J).card (J \ L).card)).det := by
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr ?_
    exact Finset.prod_ne_zero_iff.mpr fun i _ => chamberSignDiagonal_ne_zero _ _ i
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  exact (hMdet.mul hdiag).mul (hMdet.star)

/-- **Krein--Hamming rank law.**  The rank of the relative Pick defect of an ordered chamber pair is
exactly the Hamming distance between the two chambers. -/
theorem rank_universalPrimeChamberRelativePickGram (J L : Finset Nat.Primes) :
    (universalPrimeChamberRelativePickGram J L).rank = primeChamberHammingDistance J L := by
  classical
  rw [Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_det_universalPrimeChamberRelativePickGram J L))]
  simp [primeChamberHammingDistance]

/-! ## The relative Pick signature and the chamber order -/

theorem star_dotProduct_mulVec_smul {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (y : Fin N → ℂ) (c : ℂ) :
    star (c • y) ⬝ᵥ H.mulVec (c • y)
      = ((Complex.normSq c : ℝ) : ℂ) * (star y ⬝ᵥ H.mulVec y) := by
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- **Exact negative Pick index.**  The relative Pick defect of the ordered chamber pair `(J,L)` has
negative index exactly `#(J \ L)`. -/
theorem universalPrimeChamberRelativePickGram_exact_neg_inertia (J L : Finset Nat.Primes) :
    (∀ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re < 0) →
        Module.finrank ℂ W ≤ (J \ L).card) ∧
      (∃ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        Module.finrank ℂ W = (J \ L).card ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re < 0) := by
  rw [universalPrimeChamberRelativePickGram_eq]
  exact universalPrimeChamberRelativeKreinProbe_exact_neg_inertia J L

/-- **Exact positive Pick index.**  The relative Pick defect of the ordered chamber pair `(J,L)` has
positive index exactly `#(L \ J)`. -/
theorem universalPrimeChamberRelativePickGram_exact_pos_inertia (J L : Finset Nat.Primes) :
    (∀ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re) →
        Module.finrank ℂ W ≤ (L \ J).card) ∧
      (∃ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        Module.finrank ℂ W = (L \ J).card ∧
        ∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re) := by
  rw [universalPrimeChamberRelativePickGram_eq]
  exact universalPrimeChamberRelativeKreinProbe_exact_pos_inertia J L

/-- **The chamber order is analytic.**  One chamber is contained in another exactly when the
relative Pick defect has no negative direction. -/
theorem primeChamber_subset_iff_no_negative_pick_direction (J L : Finset Nat.Primes) :
    J ⊆ L ↔ ∀ y : Fin ((L \ J).card + (J \ L).card) → ℂ, y ≠ 0 →
      ¬ (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re < 0 := by
  classical
  constructor
  · intro hJL y hy hneg
    have hcard : (J \ L).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hJL)
    have hspan : Module.finrank ℂ (ℂ ∙ y) ≤ (J \ L).card := by
      refine (universalPrimeChamberRelativePickGram_exact_neg_inertia J L).1 (ℂ ∙ y) ?_
      intro x hx hxne
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have hc : c ≠ 0 := by
        intro h
        exact hxne (by simp [h])
      rw [star_dotProduct_mulVec_smul]
      have hpos : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
      have hre : (((Complex.normSq c : ℝ) : ℂ) *
          (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y)).re
          = Complex.normSq c *
            (star y ⬝ᵥ (universalPrimeChamberRelativePickGram J L).mulVec y).re := by
        simp
      rw [hre]
      exact mul_neg_of_pos_of_neg hpos hneg
    rw [finrank_span_singleton hy] at hspan
    omega
  · intro hno
    by_contra hJL
    have hne : (J \ L).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact hJL
    obtain ⟨W, hWrank, hWneg⟩ :=
      (universalPrimeChamberRelativePickGram_exact_neg_inertia J L).2
    have hWne : W ≠ ⊥ := by
      intro h
      rw [h] at hWrank
      simp only [finrank_bot] at hWrank
      exact (Finset.card_pos.mpr hne).ne' hWrank.symm
    obtain ⟨y, hyW, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    exact hno y hy (hWneg y hyW hy)

end

end GaloisForLFunctions.HTGeometry
