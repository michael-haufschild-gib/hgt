import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicLocalPrimeHeight

/-!
# Rigidity of the actual local axes and nonzero inverse fibres

Below twice a physical prime r, replacing its excluded base by a point mass
preserves the entire complementary source. Every positive r-multiple is r,
which the other distinguished tags annihilate. The actual full physical
height test has exactly the required finite Fourier support. Consequently
both mixed and fully pinned actions agree with the complete source.
Its axes/intersection term is exactly (1-r^-2) times that source; the entire
signed nonzero inverse-fibre sum is r^-2 times it. No cofactor is discarded.
The hard growing signed correlation remains in the axes action.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

private lemma phase_add (n : ℤ) (x y : ℝ) :
    ramanujanFourierPhase n (x+y)=ramanujanFourierPhase n x*ramanujanFourierPhase n y := by
  unfold ramanujanFourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_sum {ι : Type*} (s : Finset ι) (n : ℤ) (x : ι → ℝ) :
    ramanujanFourierPhase n (∑ i ∈ s, x i)=∏ i ∈ s, ramanujanFourierPhase n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ramanujanFourierPhase]
  | @insert a s ha ih => simp [ha,phase_add,ih]

private lemma product_fourier (P : Finset ℕ)
    (w : (q : RamanujanGridPrime P) → Fin (q.val^2) → ℝ) (n : ℤ) :
    (∑ x : RamanujanLocalGrid P, ((∏ q, w q (x q) : ℝ) : ℂ)*
      ramanujanFourierPhase n (ramanujanLocalGridNode x)) =
      ∏ q : RamanujanGridPrime P, ∑ k : Fin (q.val^2),
        (w q k : ℂ)*ramanujanFourierPhase n ((k.val : ℝ)/(q.val^2 : ℕ)) := by
  classical
  simp only [Complex.ofReal_prod,ramanujanLocalGridNode,phase_sum,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun q k =>
    (w q k : ℂ)*ramanujanFourierPhase n ((k.val : ℝ)/(q.val^2 : ℕ)))).symm

private lemma dirac_fourier {p : ℕ} (hp : p ≠ 0) (n : ℤ) :
    (∑ k : Fin (p^2), ((if k.val=0 then 1 else 0 : ℝ) : ℂ)*
      ramanujanFourierPhase n ((k.val : ℝ)/(p^2 : ℕ)))=1 := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp⟩
  have he (k : Fin (p^2)) : k.val=0 ↔ k=0 := by
    simpa only [Fin.val_zero] using (@Fin.ext_iff (p^2) k 0).symm
  have hc (k : Fin (p^2)) : ((if k.val=0 then 1 else 0 : ℝ) : ℂ)=
      (if k=0 then 1 else 0) := by
    by_cases h : k=0 <;> simp [he,h]
  simp only [hc,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Fin.val_zero,Nat.cast_zero,zero_div,ramanujanFourierPhase,mul_zero,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero]

private def pinned_label {P : Finset ℕ} (r p : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) : ℝ :=
  Real.log p.val * ∏ q : RamanujanGridPrime P,
    if q=r then (if (x q).val=0 then 1 else 0) else
      if q.val=p.val then ramanujanGridTag q.val (x q) else ramanujanGridBase q.val (x q)

private lemma positive_multiple {r n : ℕ} (hn : 0 < n) (hnr : n < 2*r)
    (hd : r ∣ n) : n=r := by
  rcases hd with ⟨k,rfl⟩
  have hk0 : 0 < k := by
    by_contra h
    have : k=0 := by omega
    simp only [this,mul_zero,lt_self_iff_false] at hn
  have hk2 : k < 2 := by
    by_contra h
    have hle := Nat.mul_le_mul_left r (show 2 ≤ k by omega)
    omega
  have : k=1 := by omega
  simp only [this,mul_one]

/-- Pinning the excluded prime coordinate does not change a covered sub-double-prime mode. -/
private lemma pinned_label_fourier {P : Finset ℕ} (r p : RamanujanGridPrime P)
    (hpr : p ≠ r) {n : ℕ} (hn : 0 < n) (hnr : n < 2*r.val) :
    (∑ x : RamanujanLocalGrid P, (pinned_label r p x : ℂ)*
      ramanujanFourierPhase (n : ℤ) (ramanujanLocalGridNode x)) =
      ∑ x : RamanujanLocalGrid P, (ramanujanLabelledLocalGridWeight p x : ℂ)*
        ramanujanFourierPhase (n : ℤ) (ramanujanLocalGridNode x) := by
  classical
  simp only [pinned_label,ramanujanLabelledLocalGridWeight,Complex.ofReal_mul,
    mul_assoc,← Finset.mul_sum]
  congr 1
  rw [product_fourier P (fun q k => if q=r then (if k.val=0 then 1 else 0) else
      if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k),
    product_fourier P (fun q k =>
      if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k)]
  have hrp : r.val ≠ p.val := fun h => hpr (Subtype.ext h.symm)
  have hpp := (Finset.mem_filter.mp p.property).2
  have hrprime := (Finset.mem_filter.mp r.property).2
  by_cases hd : r.val ∣ n
  · have he := positive_multiple hn hnr hd
    subst n
    have hpnd : ¬p.val ∣ r.val := fun h => hrp
      ((Nat.prime_dvd_prime_iff_eq hpp hrprime).mp h).symm
    have hp2nd : ¬p.val^2 ∣ r.val := fun h =>
      hpnd ((dvd_pow_self _ (by omega : 2 ≠ 0)).trans h)
    have hz : (∑ k : Fin (p.val^2), (ramanujanGridTag p.val k : ℂ)*
        ramanujanFourierPhase (r.val : ℤ) ((k.val : ℝ)/(p.val^2 : ℕ)))=0 := by
      rw [ramanujanGridTag_fourier hpp.ne_zero]
      simp only [Int.natAbs_natCast,ramanujanTorsionIndicator,if_neg hpnd,if_neg hp2nd,
        sub_self,Complex.ofReal_zero]
    have hl : (∏ q : RamanujanGridPrime P, ∑ k : Fin (q.val^2),
        ((if q=r then (if k.val=0 then 1 else 0) else
          if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k : ℝ) : ℂ)*
          ramanujanFourierPhase (r.val : ℤ) ((k.val : ℝ)/(q.val^2 : ℕ)))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simpa only [if_neg hpr,ite_true] using hz
    have hr : (∏ q : RamanujanGridPrime P, ∑ k : Fin (q.val^2),
        ((if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k : ℝ) : ℂ)*
          ramanujanFourierPhase (r.val : ℤ) ((k.val : ℝ)/(q.val^2 : ℕ)))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simpa only [ite_true] using hz
    exact hl.trans hr.symm
  · apply Finset.prod_congr rfl
    intro q hq
    by_cases hqr : q=r
    · subst q
      simp only [ite_true,if_neg hrp,dirac_fourier hrprime.ne_zero,
        ramanujanGridBase_fourier hrprime.ne_zero,Int.natAbs_natCast,
        ramanujanTorsionIndicator,if_neg hd,sub_zero,Complex.ofReal_one]
    · simp only [if_neg hqr]

/-- Entire complementary prime source with its r-coordinate pinned to zero. -/
def ramanujanPinnedGridWeight {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) : ℝ :=
  if (x r).val=0 then ramanujanExcludedGridCofactor r x else 0

private lemma pinned_weight_sum {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x : RamanujanLocalGrid P) :
    ramanujanPinnedGridWeight r x =
      ∑ p : RamanujanGridPrime P, if p=r then 0 else pinned_label r p x := by
  classical
  have he : ramanujanPinnedGridWeight r x =
      (if (x r).val=0 then 1 else 0)*ramanujanExcludedGridCofactor r x := by
    unfold ramanujanPinnedGridWeight
    split_ifs <;> simp only [one_mul,zero_mul]
  rw [he,ramanujanExcludedGridCofactor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpr : p=r
  · simp only [if_pos hpr,mul_zero]
  · rw [if_neg hpr,if_neg hpr,pinned_label,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    simp only [ite_true]
    have hprod : (∏ q ∈ (Finset.univ : Finset (RamanujanGridPrime P)).erase r,
        if q=r then (if (x q).val=0 then (1 : ℝ) else 0) else
          if q.val=p.val then ramanujanGridTag q.val (x q) else ramanujanGridBase q.val (x q)) =
      ∏ q ∈ (Finset.univ : Finset (RamanujanGridPrime P)).erase r,
        if q.val=p.val then ramanujanGridTag q.val (x q) else ramanujanGridBase q.val (x q) := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [if_neg (Finset.mem_erase.mp hq).1]
    rw [hprod]
    ring

/-- The complete excluded local source can be pinned at a physical prime height. -/
theorem ramanujanPinnedGridWeight_fourier {P : Finset ℕ} (r : RamanujanGridPrime P)
    {n : ℕ} (hn : 0 < n) (hnr : n < 2*r.val) :
    (∑ x : RamanujanLocalGrid P, (ramanujanPinnedGridWeight r x : ℂ)*
      ramanujanFourierPhase (n : ℤ) (ramanujanLocalGridNode x)) =
      ∑ x : RamanujanLocalGrid P, (ramanujanExcludedLocalGridWeight r x : ℂ)*
        ramanujanFourierPhase (n : ℤ) (ramanujanLocalGridNode x) := by
  classical
  simp only [pinned_weight_sum,ramanujanExcludedLocalGridWeight,Complex.ofReal_sum,Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpr : p=r
  · simp only [if_pos hpr,Complex.ofReal_zero,zero_mul]
  · simp only [if_neg hpr]
    exact pinned_label_fourier r p hpr hn hnr

private lemma phase_zero (n : ℤ) : ramanujanFourierPhase n 0=1 := by
  simp [ramanujanFourierPhase]

/-- Full tangential Fourier polynomial at one physical height. -/
def ramanujanHeightFourierTest (S : Finset ℕ) (r : ℤ) (c : ℕ → ℕ → ℂ) :
    (ℝ × ℝ × ℝ) → ℂ :=
  ∑ p ∈ S, ∑ q ∈ S, c p q • ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),r)

private def third_eval {P : Finset ℕ} (r : RamanujanGridPrime P) (x y : ℝ) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ t : RamanujanLocalGrid P, (ramanujanLabelledLocalGridWeight r t : ℂ)*
    F (x,y,ramanujanLocalGridNode t)
  map_add' F G := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring

private lemma third_eval_phase {P : Finset ℕ} (r : RamanujanGridPrime P)
    (x y : ℝ) (n : ℤ × ℤ × ℤ) :
    third_eval r x y (ramanujanTripleFourierPhase n) =
      ramanujanFourierPhase n.1 x*ramanujanFourierPhase n.2.1 y*
        (ramanujanDistinguishedPrimeEntry P r.val n.2.2.natAbs : ℂ) := by
  rw [← ramanujanLabelledLocalGridWeight_fourier P r n.2.2]
  simp only [third_eval,LinearMap.coe_mk,AddHom.coe_mk,ramanujanTripleFourierPhase,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

private lemma actual_box {N : ℝ} {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Set.Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Set.Icc N (2*N) → A v=0 := by
  intro v i hi
  have hz0 : η (v i)=0 := hz _ (fun h => hi ⟨h.1.le,h.2.le⟩)
  rw [hA]
  fin_cases i <;> simp_all [bagCubicPhysicalAmplitude,bagCubicMellinSliceValue]

/-- Exact finite Fourier support of the complete actual physical-height profile. -/
theorem bagPhysicalHeightTest_eq_finite {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Set.Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (hr : r.val ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) :
    bagPhysicalHeightTest A (r.val : ℤ) =
      ramanujanHeightFourierTest (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) (r.val : ℤ)
        (fun p q => bagCubicPhysicalAmplitude N η (bagIntegerTriple ((p : ℤ),(q : ℤ),(r.val : ℤ)))) := by
  classical
  let S := Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊
  let c := fun p q d : ℕ => bagCubicPhysicalAmplitude N η
    (bagIntegerTriple ((p : ℤ),(q : ℤ),(d : ℤ)))
  have hf : 1 ≤ ⌊N⌋₊ := by simpa using Nat.floor_mono hN.le
  have hS : ∀ n ∈ S, 1 < n ∧ n ≤ ⌊2*N⌋₊ := by
    intro n hn
    exact ⟨lt_of_le_of_lt hf (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2⟩
  have hl : (Real.log r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.log_pos (by exact_mod_cast (Finset.mem_filter.mp r.property).2.one_lt)))
  have he (x y : ℝ) : bagPhysicalHeightTest A (r.val : ℤ) (x,y,0) =
      ∑ p ∈ S, ∑ q ∈ S, c p q r.val*ramanujanFourierPhase (p : ℤ) x*
        ramanujanFourierPhase (q : ℤ) y := by
    apply mul_left_cancel₀ hl
    calc
      _ = third_eval r x y (bagLiftedFourierTest A) :=
        (bagLabelledThirdGrid_lifted hN r A (actual_box hz A hA) x y).symm
      _ = ∑ d ∈ S, ∑ p ∈ S, ∑ q ∈ S,
          c p q d*(ramanujanFourierPhase (p : ℤ) x*ramanujanFourierPhase (q : ℤ) y*
            (ramanujanDistinguishedPrimeEntry (Finset.range (⌊2*N⌋₊+1)) r.val d : ℂ)) := by
        rw [bagLiftedFourierTest_eq_finite (by linarith : 0 ≤ N) hz A hA]
        simp only [ramanujanFiniteCubeTest,map_sum,map_smul,third_eval_phase,
          Int.natAbs_natCast,smul_eq_mul,S,c]
      _ = ∑ d ∈ S, if d=r.val then (Real.log r.val : ℂ)*
          ∑ p ∈ S, ∑ q ∈ S, c p q r.val*ramanujanFourierPhase (p : ℤ) x*
            ramanujanFourierPhase (q : ℤ) y else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdC : d ∈ Finset.Icc 2 ⌊2*N⌋₊ :=
          Finset.mem_Icc.mpr ⟨by have := (hS d hd).1; omega,(hS d hd).2⟩
        have hdE := ramanujanDistinguishedPrimeEntry_band ⌊2*N⌋₊ r ⟨d,hdC⟩
        change ramanujanDistinguishedPrimeEntry (Finset.range (⌊2*N⌋₊+1)) r.val d=
          if d=r.val then Real.log r.val else 0 at hdE
        rw [hdE]
        by_cases hdr : d=r.val
        · subst d
          simp only [ite_true,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          ring
        · simp only [if_neg hdr,Complex.ofReal_zero,mul_zero,Finset.sum_const_zero]
      _ = _ := by rw [Finset.sum_ite_eq',if_pos hr]
  funext x
  calc
    _ = ramanujanFourierPhase (r.val : ℤ) x.2.2*
        bagPhysicalHeightTest A (r.val : ℤ) (x.1,x.2.1,0) := by
      simp only [bagPhysicalHeightTest,phase_zero,one_mul]
    _ = _ := by
      rw [he]
      simp only [ramanujanHeightFourierTest,Finset.sum_apply,Pi.smul_apply,
        smul_eq_mul,ramanujanTripleFourierPhase,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [c]
      ring

private def grid_pair {P : Finset ℕ} (u v : RamanujanLocalGrid P → ℝ) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    (u x : ℂ)*(v y : ℂ)*F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,0)
  map_add' F G := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring

private lemma grid_pair_phase {P : Finset ℕ} (u v : RamanujanLocalGrid P → ℝ)
    (n : ℤ × ℤ × ℤ) :
    grid_pair u v (ramanujanTripleFourierPhase n)=
      (∑ x : RamanujanLocalGrid P, (u x : ℂ)*ramanujanFourierPhase n.1 (ramanujanLocalGridNode x))*
      (∑ y : RamanujanLocalGrid P, (v y : ℂ)*ramanujanFourierPhase n.2.1 (ramanujanLocalGridNode y)) := by
  rw [Fintype.sum_mul_sum]
  simp only [grid_pair,LinearMap.coe_mk,AddHom.coe_mk,ramanujanTripleFourierPhase,phase_zero,mul_one]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- True pins that local coordinate; false retains its entire original base. -/
def ramanujanAxisPairAction {P : Finset ℕ} (r : RamanujanGridPrime P) (a b : Bool) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ :=
  grid_pair (if a then ramanujanPinnedGridWeight r else ramanujanExcludedLocalGridWeight r)
    (if b then ramanujanPinnedGridWeight r else ramanujanExcludedLocalGridWeight r)

/-- Both mixed and fully pinned actions agree throughout the exact physical frequency band. -/
theorem ramanujanAxisPairAction_heightTest {P : Finset ℕ} (r : RamanujanGridPrime P)
    (a b : Bool) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n < 2*r.val)
    (k : ℤ) (c : ℕ → ℕ → ℂ) :
    ramanujanAxisPairAction r a b (ramanujanHeightFourierTest S k c)=
      ramanujanExcludedLocalPairAction r (ramanujanHeightFourierTest S k c) := by
  change _ = grid_pair (ramanujanExcludedLocalGridWeight r)
    (ramanujanExcludedLocalGridWeight r) (ramanujanHeightFourierTest S k c)
  unfold ramanujanHeightFourierTest
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  cases a <;> cases b
  all_goals simp only [ramanujanAxisPairAction,Bool.false_eq_true,if_false,if_true,grid_pair_phase,
    ramanujanPinnedGridWeight_fourier r (hS p hp).1 (hS p hp).2,
    ramanujanPinnedGridWeight_fourier r (hS q hq).1 (hS q hq).2]

/-- Actual full physical-height source is unchanged by either or both local pins. -/
theorem bagPhysicalHeightTest_axisPair {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Set.Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (hr : r.val ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊)
    (a b : Bool) :
    ramanujanAxisPairAction r a b (bagPhysicalHeightTest A (r.val : ℤ))=
      ramanujanExcludedLocalPairAction r (bagPhysicalHeightTest A (r.val : ℤ)) := by
  rw [bagPhysicalHeightTest_eq_finite hN hz A hA r hr]
  apply ramanujanAxisPairAction_heightTest
  intro n hn
  have hnf := Finset.mem_Ioc.mp hn
  have hrf := Finset.mem_Ioc.mp hr
  have hrN : N < (r.val : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ N)).mp hrf.1
  have hn2 : (n : ℝ) ≤ 2*N := (Nat.le_floor_iff (by linarith : 0 ≤ 2*N)).mp hnf.2
  have hlt : (n : ℝ) < 2*(r.val : ℝ) := by linarith
  refine ⟨by omega,?_⟩
  exact_mod_cast hlt

private lemma sum_four_comm {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)=∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

private lemma weighted_profile {P : Finset ℕ} (r : RamanujanGridPrime P)
    (u v : Fin (r.val^2) → ℂ) (F : (ℝ × ℝ × ℝ) → ℂ) :
    (∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
      u (x r)*v (y r)*(ramanujanExcludedGridCofactor r x : ℂ)*
        (ramanujanExcludedGridCofactor r y : ℂ)*
        F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,0)) =
      ∑ k, ∑ l, u k*v l*ramanujanExcludedGridProfile r F k l := by
  classical
  unfold ramanujanExcludedGridProfile
  simp only [Finset.mul_sum]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [ite_and,mul_ite,mul_zero,Finset.sum_ite_irrel,Finset.sum_ite_eq,
    Finset.mem_univ,if_true,Finset.sum_const_zero]
  ring

private def axis_factor {P : Finset ℕ} (r : RamanujanGridPrime P) (a : Bool)
    (k : Fin (r.val^2)) : ℝ :=
  if a then (if k.val=0 then 1 else 0) else ramanujanGridBase r.val k

private lemma axis_weight_factor {P : Finset ℕ} (r : RamanujanGridPrime P)
    (a : Bool) (x : RamanujanLocalGrid P) :
    (if a then ramanujanPinnedGridWeight r else ramanujanExcludedLocalGridWeight r) x=
      axis_factor r a (x r)*ramanujanExcludedGridCofactor r x := by
  cases a
  · exact ramanujanExcludedLocalGridWeight_factor r x
  · change (if (x r).val=0 then ramanujanExcludedGridCofactor r x else 0)=
      (if (x r).val=0 then 1 else 0)*ramanujanExcludedGridCofactor r x
    split_ifs <;> simp only [one_mul,zero_mul]

private lemma axis_pair_profile {P : Finset ℕ} (r : RamanujanGridPrime P)
    (a b : Bool) (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanAxisPairAction r a b F =
      ∑ k, ∑ l, (axis_factor r a k : ℂ)*(axis_factor r b l : ℂ)*
        ramanujanExcludedGridProfile r F k l := by
  change (∑ x : RamanujanLocalGrid P, ∑ y : RamanujanLocalGrid P,
    (((if a then ramanujanPinnedGridWeight r else ramanujanExcludedLocalGridWeight r) x : ℝ) : ℂ)*
    (((if b then ramanujanPinnedGridWeight r else ramanujanExcludedLocalGridWeight r) y : ℝ) : ℂ)*
      F (ramanujanLocalGridNode x,ramanujanLocalGridNode y,0)) = _
  simp only [axis_weight_factor,Complex.ofReal_mul]
  rw [← weighted_profile]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

private abbrev as_prime {P : Finset ℕ} (r : RamanujanGridPrime P) : Nat.Primes :=
  ⟨r.val,(Finset.mem_filter.mp r.property).2⟩

private lemma dirac_sum (p : Nat.Primes) (F : Fin ((p : ℕ)^2) → ℂ) :
    (∑ k, ((if k.val=0 then 1 else 0 : ℝ) : ℂ)*F k)=F (criticalDefectGridNode p 0) := by
  letI : NeZero ((p : ℕ)^2) := ⟨pow_ne_zero 2 p.property.ne_zero⟩
  have hz : criticalDefectGridNode p 0=(0 : Fin ((p : ℕ)^2)) := by
    apply Fin.ext
    simp [criticalDefectGridNode]
  have he (k : Fin ((p : ℕ)^2)) : k.val=0 ↔ k=0 := by
    simpa only [Fin.val_zero] using (@Fin.ext_iff ((p : ℕ)^2) k 0).symm
  have hc (k : Fin ((p : ℕ)^2)) : ((if k.val=0 then 1 else 0 : ℝ) : ℂ)=
      (if k=0 then 1 else 0) := by
    by_cases h : k=0 <;> simp [he,h]
  rw [hz]
  simp only [hc,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private lemma axis_pair_tt {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanAxisPairAction r true true F=ramanujanExcludedGridProfile r F
      (criticalDefectGridNode (as_prime r) 0) (criticalDefectGridNode (as_prime r) 0) := by
  rw [axis_pair_profile]
  simp only [axis_factor,if_true]
  simp_rw [mul_assoc,← Finset.mul_sum,dirac_sum (as_prime r)]

private lemma axis_pair_ft {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanAxisPairAction r false true F=∑ a : ZMod (as_prime r : ℕ),
      criticalDefectBase (as_prime r) a*ramanujanExcludedGridProfile r F
        (criticalDefectGridNode (as_prime r) a) (criticalDefectGridNode (as_prime r) 0) := by
  rw [axis_pair_profile]
  simp only [axis_factor,Bool.false_eq_true,if_false,if_true]
  simp_rw [mul_assoc,← Finset.mul_sum,dirac_sum (as_prime r)]
  exact criticalDefectGridBase_sum (as_prime r) _

private lemma axis_pair_tf {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanAxisPairAction r true false F=∑ b : ZMod (as_prime r : ℕ),
      criticalDefectBase (as_prime r) b*ramanujanExcludedGridProfile r F
        (criticalDefectGridNode (as_prime r) 0) (criticalDefectGridNode (as_prime r) b) := by
  rw [axis_pair_profile]
  simp only [axis_factor,Bool.false_eq_true,if_false,if_true]
  simp_rw [mul_assoc,← Finset.mul_sum,dirac_sum (as_prime r)]
  exact criticalDefectGridBase_sum (as_prime r) _

private lemma sum_field (p : Nat.Primes) (f : ZMod (p : ℕ) → ℂ) :
    (∑ a, f a)=f 0+∑ u : (ZMod (p : ℕ))ˣ, f u := by
  rw [RHTower.sum_units_eq_sum_ite]
  calc
    _ = ∑ a : ZMod (p : ℕ),
        ((if a=0 then f 0 else 0)+(if a=0 then 0 else f a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a=0 <;> simp [h]
    _ = _ := by simp [Finset.sum_add_distrib]

private lemma axes_weighted (p : Nat.Primes) (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) :
    criticalProfileAxes p H=(1-(p : ℂ)⁻¹)*
      ((∑ a, criticalDefectBase p a*H a 0)+(∑ b, criticalDefectBase p b*H 0 b))-
        (1-(p : ℂ)⁻¹)^2*H 0 0 := by
  rw [sum_field p (fun a => criticalDefectBase p a*H a 0),
    sum_field p (fun b => criticalDefectBase p b*H 0 b)]
  simp only [criticalProfileAxes,criticalDefectBase,if_true,if_neg (Units.ne_zero _),
    zero_sub,neg_mul,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_neg_distrib]
  ring

/-- The full local axes and intersection of the actual dephased profile. -/
def ramanujanLocalAxesAction {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) : ℂ :=
  criticalProfileAxes (as_prime r) (fun a b => ramanujanExcludedGridDephasedProfile r F
    (criticalDefectGridNode (as_prime r) a) (criticalDefectGridNode (as_prime r) b))

/-- Every nonzero inverse fibre, with its original sign and character. -/
def ramanujanLocalNonzeroAction {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) : ℂ :=
  let p := as_prime r
  ∑ d : ZMod (p : ℕ), if d=0 then 0 else (r.val : ℂ)⁻¹^2*
    criticalProfileInverse p (fun a b => ramanujanExcludedGridDephasedProfile r F
      (criticalDefectGridNode p a) (criticalDefectGridNode p b)) d*ZMod.stdAddChar d

private lemma dephase_axis_left {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) (a : ZMod (as_prime r : ℕ)) :
    ramanujanExcludedGridDephasedProfile r F (criticalDefectGridNode (as_prime r) a)
      (criticalDefectGridNode (as_prime r) 0) =
    ramanujanExcludedGridProfile r F (criticalDefectGridNode (as_prime r) a)
      (criticalDefectGridNode (as_prime r) 0) := by
  simp [ramanujanExcludedGridDephasedProfile,criticalDefectGridNode,phase_zero]

private lemma dephase_axis_right {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) (b : ZMod (as_prime r : ℕ)) :
    ramanujanExcludedGridDephasedProfile r F (criticalDefectGridNode (as_prime r) 0)
      (criticalDefectGridNode (as_prime r) b) =
    ramanujanExcludedGridProfile r F (criticalDefectGridNode (as_prime r) 0)
      (criticalDefectGridNode (as_prime r) b) := by
  simp [ramanujanExcludedGridDephasedProfile,criticalDefectGridNode,phase_zero]

/-- Axes are the exact inclusion-exclusion of the two mixed and fully pinned sources. -/
theorem ramanujanLocalAxesAction_eq {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanLocalAxesAction r F=(1-(r.val : ℂ)⁻¹)*
      (ramanujanAxisPairAction r false true F+ramanujanAxisPairAction r true false F)-
        (1-(r.val : ℂ)⁻¹)^2*ramanujanAxisPairAction r true true F := by
  rw [ramanujanLocalAxesAction,axes_weighted]
  simp only [dephase_axis_left,dephase_axis_right,axis_pair_ft,axis_pair_tf,axis_pair_tt]

theorem ramanujanExcludedInverseProfileAction_split {P : Finset ℕ} (r : RamanujanGridPrime P)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanExcludedInverseProfileAction r F=
      ramanujanLocalAxesAction r F+ramanujanLocalNonzeroAction r F := by
  unfold ramanujanExcludedInverseProfileAction ramanujanLocalNonzeroAction
  change (∑ d : ZMod (as_prime r : ℕ),
    (if d=0 then ramanujanLocalAxesAction r F else (r.val : ℂ)⁻¹^2*
      criticalProfileInverse (as_prime r) (fun a b => ramanujanExcludedGridDephasedProfile r F
        (criticalDefectGridNode (as_prime r) a) (criticalDefectGridNode (as_prime r) b)) d)*
      ZMod.stdAddChar d) = _
  have he (d : ZMod (as_prime r : ℕ)) :
      (if d=0 then ramanujanLocalAxesAction r F else (r.val : ℂ)⁻¹^2*
        criticalProfileInverse (as_prime r) (fun a b => ramanujanExcludedGridDephasedProfile r F
          (criticalDefectGridNode (as_prime r) a) (criticalDefectGridNode (as_prime r) b)) d)*
        ZMod.stdAddChar d =
      (if d=0 then ramanujanLocalAxesAction r F else 0)+
        (if d=0 then 0 else (r.val : ℂ)⁻¹^2*
          criticalProfileInverse (as_prime r) (fun a b => ramanujanExcludedGridDephasedProfile r F
            (criticalDefectGridNode (as_prime r) a) (criticalDefectGridNode (as_prime r) b)) d*
          ZMod.stdAddChar d) := by
    by_cases hd : d=0 <;> simp [hd]
  simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- At every actual prime height, the axes carry this exact fraction of the full source. -/
theorem bagPhysicalHeightTest_axes {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Set.Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (hr : r.val ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) :
    ramanujanLocalAxesAction r (bagPhysicalHeightTest A (r.val : ℤ))=
      (1-(r.val : ℂ)⁻¹^2)*ramanujanExcludedInverseProfileAction r
        (bagPhysicalHeightTest A (r.val : ℤ)) := by
  rw [ramanujanLocalAxesAction_eq]
  simp only [bagPhysicalHeightTest_axisPair hN hz A hA r hr,
    ramanujanExcludedLocalPairAction_inverse]
  ring

/-- The COMPLETE nonzero inverse-fibre action retains precisely the residual fraction. -/
theorem bagPhysicalHeightTest_nonzero {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Set.Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (hr : r.val ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) :
    ramanujanLocalNonzeroAction r (bagPhysicalHeightTest A (r.val : ℤ))=
      (r.val : ℂ)⁻¹^2*ramanujanExcludedInverseProfileAction r
        (bagPhysicalHeightTest A (r.val : ℤ)) := by
  have he := ramanujanExcludedInverseProfileAction_split r (bagPhysicalHeightTest A (r.val : ℤ))
  have ha := bagPhysicalHeightTest_axes hN hz A hA r hr
  rw [ha] at he
  linear_combination -he

open Set Filter
open scoped Topology ContDiff

/-- Unconditional actual family with exact axes/nonzero-channel rigidity and the original error. -/
theorem exists_bagPhysicalLocalAxisFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N)=bagLocalPrimeHeightInverseAction N (A N) ∧
        ∀ r : RamanujanBandPrime ⌊2*(N : ℝ)⌋₊, r.val ∈ Finset.Ioc ⌊(N : ℝ)⌋₊ ⌊2*(N : ℝ)⌋₊ →
          ramanujanLocalAxesAction r (bagPhysicalHeightTest (A N) (r.val : ℤ))=
            (1-(r.val : ℂ)⁻¹^2)*ramanujanExcludedInverseProfileAction r
              (bagPhysicalHeightTest (A N) (r.val : ℤ)) ∧
          ramanujanLocalNonzeroAction r (bagPhysicalHeightTest (A N) (r.val : ℤ))=
            (r.val : ℂ)⁻¹^2*ramanujanExcludedInverseProfileAction r
              (bagPhysicalHeightTest (A N) (r.val : ℤ))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-bagLocalPrimeHeightInverseAction N (A N)‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hreg,herr⟩ := exists_bagLocalPrimeHeightInverseFamily
  refine ⟨η,A,?_,herr⟩
  filter_upwards [hreg,eventually_ge_atTop (2 : ℕ)] with N h hN
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2,?_⟩
  intro r hr
  have hN' : (1 : ℝ)<N := by exact_mod_cast (by omega : 1 < N)
  exact ⟨bagPhysicalHeightTest_axes hN' h.2.2.2.1 (A N) h.2.2.2.2.2.1 r hr,
    bagPhysicalHeightTest_nonzero hN' h.2.2.2.1 (A N) h.2.2.2.2.2.1 r hr⟩

end RHTower.BAGTrace
