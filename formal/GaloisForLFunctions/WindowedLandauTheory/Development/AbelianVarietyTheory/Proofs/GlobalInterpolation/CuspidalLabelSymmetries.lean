import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalLabelUniqueness

/-! Galois conjugates of cuspidal characters carry the transformed prime labels.
The minimum polynomial of a transformed root has the transformed Frobenius orbit. -/

noncomputable section
open Polynomial IntermediateField WindowedLandauTheory.CyclotomicNorms GlobalTheory.GreenBridge
open GlobalTheory.GreenExists
open scoped Classical

namespace GlobalTheory.GLq

variable {g d : ℕ} [Fact g.Prime]

/-- An injective Galois-equivariant map on the roots gives all the roots of the new label. -/
theorem rootsBar_minpoly_transform {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {w : Fbar g}
    (hw : w ∈ rootsBar P) (F : Fbar g → Fbar g) (hF : F w ≠ 0)
    (hcomm : ∀ (σ : Fbar g ≃ₐ[ZMod g] Fbar g) (x : Fbar g), F (σ x) = σ (F x))
    (hinj : Set.InjOn F {x | x ∈ rootsBar P}) :
    IsPrimeLab d (minpoly (ZMod g) (F w)) ∧
      rootsBar (minpoly (ZMod g) (F w)) = (rootsBar P).map F := by
  let Q := minpoly (ZMod g) (F w)
  have hint : IsIntegral (ZMod g) (F w) := Algebra.IsIntegral.isIntegral _
  have hmin : P = minpoly (ZMod g) w :=
    minpoly.eq_of_irreducible_of_monic hP.2.1 ((mem_rootsBar_iff hP.1.ne_zero).mp hw) hP.1
  have hQ0 : Q ≠ 0 := minpoly.ne_zero hint
  have hPnd : (rootsBar P).Nodup :=
    (nodup_aroots_iff_of_splits hP.1.ne_zero (IsAlgClosed.splits _)).mpr
      (PerfectField.separable_of_irreducible hP.2.1)
  have hQnd : (rootsBar Q).Nodup :=
    (nodup_aroots_iff_of_splits hQ0 (IsAlgClosed.splits _)).mpr
      (PerfectField.separable_of_irreducible (minpoly.irreducible hint))
  have he : rootsBar Q = (rootsBar P).map F := by
    refine (Multiset.Nodup.ext hQnd (Multiset.Nodup.map_on hinj hPnd)).2 fun z => ?_
    rw [mem_rootsBar_iff hQ0, Multiset.mem_map]
    constructor
    · intro hz
      obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic (F w)) hz
      refine ⟨σ.symm w, (mem_rootsBar_iff hP.1.ne_zero).mpr ?_, ?_⟩
      · change aeval (σ.symm.toAlgHom w) P = 0
        rw [Polynomial.aeval_algHom_apply, (mem_rootsBar_iff hP.1.ne_zero).mp hw, map_zero]
      · rw [hcomm, ← hσ, AlgEquiv.symm_apply_apply]
    · rintro ⟨r, hr, rfl⟩
      have hroot := (mem_rootsBar_iff hP.1.ne_zero).mp hr
      rw [hmin] at hroot
      obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic w) hroot
      change aeval (F r) (minpoly (ZMod g) (F w)) = 0
      have hpoly : minpoly (ZMod g) (σ (F r)) = minpoly (ZMod g) (F r) :=
        minpoly.algHom_eq σ.toAlgHom σ.injective (F r)
      rw [← hσ, hcomm σ r, hpoly]
      exact minpoly.aeval _ _
  refine ⟨⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.coeff_zero_ne_zero hint hF, ?_⟩, he⟩
  have hcard (P : (ZMod g)[X]) : (rootsBar P).card = P.natDegree := by
    rw [rootsBar, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  change Q.natDegree = d
  rw [← hcard Q, he, Multiset.card_map, hcard, hP.2.2.2]

private theorem thetaOf_ringEquiv (L : LabelDatum g) (α : ℂ ≃+* ℂ) {x y : Fbar g}
    (h : α (L.teich x) = L.teich y) (z : Fbar g) :
    α (thetaOf L d x z) = thetaOf L d y z := by
  unfold thetaOf
  split_ifs
  · rw [map_pow, h]
  · exact map_zero α

/-- If a field automorphism raises the relevant roots of unity to the power `a`,
the cuspidal label roots are raised to the same power. -/
theorem rootsBar_of_cuspidal_galois (L : LabelDatum g) (hg : 5 ≤ g) (α : ℂ ≃+* ℂ) (a : ℕ)
    (hα : ∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (g ^ e - 1)) = 1 → α ζ = ζ ^ a)
    {P P' : (ZMod g)[X]} {χ χ' : Gn g d → ℂ}
    (hP : IsCuspOf L P χ) (hP' : IsCuspOf L P' χ') (hχ : ∀ γ, χ' γ = α (χ γ)) :
    rootsBar P' = (rootsBar P).map (· ^ a) := by
  have hd := hP.2.1.1
  have hu {x : Fbar g} (hx : x ∈ rootsBar P) : x ^ (g ^ d - 1) = 1 :=
    root_unit hP.1 ((mem_rootsBar_iff hP.1.1.ne_zero).mp hx)
  have hn {x : Fbar g} (hx : x ∈ rootsBar P) : x ≠ 0 := by
    intro he
    have h := hu hx
    rw [he, zero_pow (N_pos' hd).ne'] at h
    exact zero_ne_one h
  have hteich (x : Fbar g) (hx : x ∈ rootsBar P) : α (L.teich x) = L.teich (x ^ a) := by
    obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem (fun e => g ^ e - 1)
      (Finset.mem_Icc.mpr ⟨hd, le_rfl⟩)
    have he : L.teich x ^ (∏ e ∈ Finset.Icc 1 d, (g ^ e - 1)) = 1 := by
      rw [hj, pow_mul, ← map_pow, hu hx, map_one, one_pow]
    rw [hα _ he, map_pow]
  let w := rootOf P
  have hw : w ∈ rootsBar P := (mem_rootsBar_iff hP.1.1.ne_zero).mpr (rootOf_spec hP.1)
  have hinj : Set.InjOn (fun x : Fbar g => x ^ a) {x | x ∈ rootsBar P} := by
    intro x hx y hy h
    change x ^ a = y ^ a at h
    apply L.teich_inj x y (hn hx) (hn hy)
    apply α.injective
    rw [hteich x hx, hteich y hy, h]
  obtain ⟨hR, hRoots⟩ := rootsBar_minpoly_transform hP.1 hw (fun x => x ^ a)
    (pow_ne_zero a (hn hw)) (fun σ x => (map_pow σ x a).symm) hinj
  have hRχ : IsCuspOf L (minpoly (ZMod g) (w ^ a)) χ' := by
    refine ⟨hR, hP'.2.1, ?_⟩
    intro r hr γ hγ z hz
    rw [hRoots, Multiset.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [hχ, hP.2.2 x hx γ hγ z hz]
    simp only [map_mul, map_pow, map_neg, map_one, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => thetaOf_ringEquiv L α (d := d) (hteich x hx) _)
  rw [isCuspOf_label_eq L hg hP' hRχ]
  exact hRoots

/-- An irreducible characteristic polynomial of an invertible matrix is a prime label. -/
theorem isPrimeLab_charpoly (γ : Gn g d) (hγ : Irreducible γ.val.charpoly) :
    IsPrimeLab d γ.val.charpoly := by
  have hdet : γ.val.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero γ
  refine ⟨Matrix.charpoly_monic _, hγ, ?_, by simp⟩
  intro hz
  exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, hz, mul_zero])

private theorem root_charpoly_inv (γ : Gn g d) {z : Fbar g} (hz0 : z ≠ 0)
    (hz : aeval z γ.val.charpoly = 0) : aeval z⁻¹ (γ⁻¹).val.charpoly = 0 := by
  let f := algebraMap (ZMod g) (Fbar g)
  have he (M : Mt g d) (u : Fbar g) :
      aeval u M.charpoly = (Matrix.scalar (Fin d) u - M.map f).det := by
    rw [← Polynomial.eval_map_algebraMap, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  have hAB : (γ⁻¹).val.map f * γ.val.map f = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  rw [he] at hz ⊢
  have hs (u : Fbar g) : Matrix.scalar (Fin d) u = u • (1 : Matrix (Fin d) (Fin d) (Fbar g)) := by
    simp [Matrix.smul_one_eq_diagonal]
  have hmat : Matrix.scalar (Fin d) z⁻¹ - (γ⁻¹).val.map f =
      -(z⁻¹ • (γ⁻¹).val.map f) * (Matrix.scalar (Fin d) z - γ.val.map f) := by
    rw [hs, hs, neg_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hz0, one_smul, Matrix.smul_mul, hAB]
    abel
  rw [hmat, Matrix.det_mul, hz, mul_zero]

private theorem irreducible_charpoly_inv (γ : Gn g d) (hγ : Irreducible γ.val.charpoly)
    {z : Fbar g} (hz0 : z ≠ 0) (hz : z ∈ rootsBar γ.val.charpoly) :
    Irreducible (γ⁻¹).val.charpoly := by
  have h := (rootsBar_minpoly_transform (isPrimeLab_charpoly γ hγ) hz Inv.inv (inv_ne_zero hz0)
    (fun σ y => (map_inv₀ σ y).symm) (fun _ _ _ _ e => inv_injective e)).1
  have hroot := root_charpoly_inv γ hz0 ((mem_rootsBar_iff hγ.ne_zero).mp hz)
  have hdiv := minpoly.dvd (ZMod g) z⁻¹ hroot
  have he := Polynomial.eq_of_monic_of_dvd_of_natDegree_le h.1 (Matrix.charpoly_monic (γ⁻¹).val)
    hdiv (by rw [h.2.2.2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  rw [he]
  exact h.2.1

private theorem inv_eq_pow_pred {z : Fbar g} {m : ℕ} (hm : 0 < m) (hz : z ^ m = 1) :
    z⁻¹ = z ^ (m - 1) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rwa [← pow_succ, Nat.sub_add_cancel hm]

private theorem thetaOf_inv (L : LabelDatum g) (hd : 0 < d) {x z : Fbar g}
    (hx : x ^ (g ^ d - 1) = 1) (hz : z ^ (g ^ d - 1) = 1) :
    thetaOf L d x⁻¹ z = thetaOf L d x z⁻¹ := by
  rw [inv_eq_pow_pred (N_pos' hd) hx, thetaOf_pow L hd hx hz, ← inv_eq_pow_pred (N_pos' hd) hz]

/-- A contragredient cuspidal character has the reciprocal label roots. -/
theorem rootsBar_of_cuspidal_dual (L : LabelDatum g) (hg : 5 ≤ g)
    {P P' : (ZMod g)[X]} {χ χ' : Gn g d → ℂ}
    (hP : IsCuspOf L P χ) (hP' : IsCuspOf L P' χ') (hχ : ∀ γ, χ' γ = χ γ⁻¹) :
    rootsBar P' = (rootsBar P).map Inv.inv := by
  have hd := hP.2.1.1
  let w := rootOf P
  have hw : w ∈ rootsBar P := (mem_rootsBar_iff hP.1.1.ne_zero).mpr (rootOf_spec hP.1)
  have hw0 : w ≠ 0 := by
    intro he
    have h := root_unit hP.1 (rootOf_spec hP.1)
    change w ^ (g ^ d - 1) = 1 at h
    rw [he, zero_pow (N_pos' hd).ne'] at h
    exact zero_ne_one h
  obtain ⟨hR, hRoots⟩ := rootsBar_minpoly_transform hP.1 hw Inv.inv (inv_ne_zero hw0)
    (fun σ x => (map_inv₀ σ x).symm) (fun _ _ _ _ e => inv_injective e)
  have hRχ : IsCuspOf L (minpoly (ZMod g) w⁻¹) χ' := by
    refine ⟨hR, hP'.2.1, ?_⟩
    intro r hr γ hγ z hz
    rw [hRoots, Multiset.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hzu := root_unit (isPrimeLab_charpoly γ hγ) ((mem_rootsBar_iff hγ.ne_zero).mp hz)
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, zero_pow (N_pos' hd).ne'] at hzu
      exact zero_ne_one hzu
    have hγi := irreducible_charpoly_inv γ hγ hz0 hz
    have hzi : z⁻¹ ∈ rootsBar (γ⁻¹).val.charpoly := (mem_rootsBar_iff hγi.ne_zero).mpr
      (root_charpoly_inv γ hz0 ((mem_rootsBar_iff hγ.ne_zero).mp hz))
    rw [hχ, hP.2.2 x hx γ⁻¹ hγi z⁻¹ hzi]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inv_pow, thetaOf_inv L hd
      (root_unit hP.1 ((mem_rootsBar_iff hP.1.1.ne_zero).mp hx)) (unit_pow hzu _)]
  rw [isCuspOf_label_eq L hg hP' hRχ]
  exact hRoots

private theorem det_eq_root_pow_sum (γ : Gn g d) (hγ : Irreducible γ.val.charpoly)
    {z : Fbar g} (hz : aeval z γ.val.charpoly = 0) :
    algebraMap (ZMod g) (Fbar g) γ.val.det = z ^ ∑ i ∈ Finset.range d, g ^ i := by
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have hmin : γ.val.charpoly = minpoly (ZMod g) z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hd : (minpoly (ZMod g) z).natDegree = d := by
    rw [← hmin, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let pb := IntermediateField.adjoin.powerBasis hi
  have hnorm : Algebra.norm (ZMod g) pb.gen = γ.val.det := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, Matrix.det_eq_sign_charpoly_coeff, hmin]
    have hdim : pb.dim = d := (IntermediateField.adjoin.powerBasis_dim hi).trans hd
    rw [hdim, IntermediateField.adjoin.powerBasis_gen hi, IntermediateField.minpoly_gen]
    simp only [Fintype.card_fin]
  letI : FiniteDimensional (ZMod g) ((ZMod g)⟮z⟯) := IntermediateField.adjoin.finiteDimensional hi
  letI : Finite ((ZMod g)⟮z⟯) := Module.finite_of_finite (ZMod g)
  have hfr : Module.finrank (ZMod g) ((ZMod g)⟮z⟯) = d := (IntermediateField.adjoin.finrank hi).trans hd
  have h := FiniteField.algebraMap_norm_eq_pow_sum (K := ZMod g) (L := (ZMod g)⟮z⟯) (x := pb.gen)
  rw [hnorm, hfr, Nat.card_zmod] at h
  have hpow : ((pb.gen ^ ∑ i ∈ Finset.range d, g ^ i : (ZMod g)⟮z⟯) : Fbar g) =
      z ^ ∑ i ∈ Finset.range d, g ^ i := by
    rw [IntermediateField.coe_pow, IntermediateField.adjoin.powerBasis_gen hi,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← hpow, ← h]
  rfl

private theorem gen_one_pow_eq_det (L : LabelDatum g) (hd : 0 < d)
    (γ : Gn g d) (hγ : Irreducible γ.val.charpoly)
    {z : Fbar g} {m : ℕ} (hz : aeval z γ.val.charpoly = 0) (hm : L.gen d ^ m = z) :
    L.gen 1 ^ m = algebraMap (ZMod g) (Fbar g) γ.val.det := by
  have hnorm := L.gen_norm 1 d Nat.zero_lt_one hd
  rw [one_mul, pow_one] at hnorm
  rw [det_eq_root_pow_sum γ hγ hz, ← hnorm, ← hm, Nat.geomSum_eq (Fact.out : g.Prime).one_lt,
    ← pow_mul, ← pow_mul, mul_comm]

private theorem thetaOf_mul (L : LabelDatum g) (x y z : Fbar g) :
    thetaOf L d (x * y) z = thetaOf L d x z * thetaOf L d y z := by
  unfold thetaOf
  split_ifs
  · rw [map_mul, mul_pow]
  · exact (zero_mul _).symm

/-- The determinant twist multiplies the label roots by its scalar. -/
theorem rootsBar_of_cuspidal_twist (L : LabelDatum g) (hg : 5 ≤ g)
    {P P' : (ZMod g)[X]} {χ χ' : Gn g d → ℂ}
    (hP : IsCuspOf L P χ) (hP' : IsCuspOf L P' χ') (t : ZMod g) (ht : t ≠ 0)
    (hχ : ∀ (γ : Gn g d) (m : ℕ), L.gen 1 ^ m = algebraMap (ZMod g) (Fbar g) γ.val.det →
      χ' γ = L.teich (algebraMap (ZMod g) (Fbar g) t) ^ m * χ γ) :
    rootsBar P' = (rootsBar P).map (· * algebraMap (ZMod g) (Fbar g) t) := by
  have hd := hP.2.1.1
  let T := algebraMap (ZMod g) (Fbar g) t
  have hT : T ≠ 0 := (map_ne_zero (algebraMap (ZMod g) (Fbar g))).mpr ht
  have hTp : T ^ (g ^ d - 1) = 1 := by
    obtain ⟨k, hk⟩ : (g - 1) ∣ g ^ d - 1 := by
      simpa only [pow_one] using Nat.pow_sub_one_dvd_pow_sub_one g (one_dvd d)
    rw [hk, pow_mul]
    change ((algebraMap (ZMod g) (Fbar g) t) ^ (g - 1)) ^ k = 1
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one ht, map_one, one_pow]
  have hfix (i : ℕ) : T ^ g ^ i = T := by
    change (algebraMap (ZMod g) (Fbar g) t) ^ g ^ i = algebraMap (ZMod g) (Fbar g) t
    rw [← map_pow, ZMod.pow_card_pow]
  let w := rootOf P
  have hw : w ∈ rootsBar P := (mem_rootsBar_iff hP.1.1.ne_zero).mpr (rootOf_spec hP.1)
  have hw0 : w ≠ 0 := by
    intro he
    have h := root_unit hP.1 (rootOf_spec hP.1)
    change w ^ (g ^ d - 1) = 1 at h
    rw [he, zero_pow (N_pos' hd).ne'] at h
    exact zero_ne_one h
  obtain ⟨hR, hRoots⟩ := rootsBar_minpoly_transform hP.1 hw (· * T) (mul_ne_zero hw0 hT)
    (fun σ x => by
      rw [map_mul, show σ T = T from σ.commutes t])
    (fun _ _ _ _ h => mul_right_cancel₀ hT h)
  have hRχ : IsCuspOf L (minpoly (ZMod g) (w * T)) χ' := by
    refine ⟨hR, hP'.2.1, ?_⟩
    intro r hr γ hγ z hz
    rw [hRoots, Multiset.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hroot := (mem_rootsBar_iff hγ.ne_zero).mp hz
    have hzpow := root_unit (isPrimeLab_charpoly γ hγ) hroot
    letI : NeZero (g ^ d - 1) := ⟨(N_pos' hd).ne'⟩
    obtain ⟨m, _, hm⟩ := (gen_prim L hd).eq_pow_of_pow_eq_one hzpow
    have hdet := gen_one_pow_eq_det L hd γ hγ hroot hm
    rw [hχ γ m hdet, hP.2.2 x hx γ hγ z hz, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hTθ : thetaOf L d T (z ^ g ^ i) = L.teich T ^ m := by
      rw [← hm, ← pow_mul, thetaOf_gen_pow L hd T (by rw [← map_pow, hTp, map_one])]
      rw [mul_comm m, pow_mul, ← map_pow, hfix i]
    rw [thetaOf_mul, hTθ, mul_comm]
  rw [isCuspOf_label_eq L hg hP' hRχ]
  exact hRoots

/-- In rank one, the determinant character associated with `t` has label `X - C t`. -/
theorem cuspLabel_rank_one (L : LabelDatum g) (hg : 5 ≤ g)
    {P : (ZMod g)[X]} {χ : Gn g 1 → ℂ} (hP : IsCuspOf L P χ)
    (t : ZMod g) (ht : t ≠ 0)
    (hχ : ∀ (γ : Gn g 1) (m : ℕ), L.gen 1 ^ m = algebraMap (ZMod g) (Fbar g) γ.val.det →
      χ γ = L.teich (algebraMap (ZMod g) (Fbar g) t) ^ m) :
    P = X - C t := by
  have hP' : IsPrimeLab 1 (X - C t) :=
    ⟨monic_X_sub_C t, irreducible_X_sub_C t, by simpa using ht, by simp⟩
  apply isCuspOf_label_eq L hg hP
  refine ⟨hP', hP.2.1, ?_⟩
  intro x hx γ hγ z hz
  have hxt : x = algebraMap (ZMod g) (Fbar g) t := by
    simpa only [map_sub, aeval_X, aeval_C, sub_eq_zero] using
      (mem_rootsBar_iff hP'.1.ne_zero).mp hx
  have hzdet : z = algebraMap (ZMod g) (Fbar g) γ.val.det := by
    have hp : γ.val.charpoly = X - C γ.val.det := by
      rw [Matrix.charpoly, Matrix.det_unique, Matrix.det_unique, Fin.default_eq_zero, Matrix.charmatrix_apply_eq]
    have hr := (mem_rootsBar_iff hγ.ne_zero).mp hz
    rw [hp] at hr
    simpa only [map_sub, aeval_X, aeval_C, sub_eq_zero] using hr
  have hz1 := root_unit (isPrimeLab_charpoly γ hγ) ((mem_rootsBar_iff hγ.ne_zero).mp hz)
  letI : NeZero (g ^ 1 - 1) := ⟨(N_pos' (g := g) Nat.zero_lt_one).ne'⟩
  obtain ⟨m, _, hm⟩ := (gen_prim L Nat.zero_lt_one).eq_pow_of_pow_eq_one hz1
  rw [hχ γ m (hm.trans hzdet), hxt, ← hm]
  simp only [Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one]
  have hxtpow : (algebraMap (ZMod g) (Fbar g) t) ^ (g ^ 1 - 1) = 1 := by
    rw [pow_one, ← map_pow, ZMod.pow_card_sub_one_eq_one ht, map_one]
  exact (thetaOf_gen_pow L Nat.zero_lt_one _ (by rw [← map_pow, hxtpow, map_one]) m).symm

end GlobalTheory.GLq
