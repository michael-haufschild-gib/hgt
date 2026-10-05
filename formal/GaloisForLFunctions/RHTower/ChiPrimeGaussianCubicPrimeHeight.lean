import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPartialPoisson
import GaloisForLFunctions.RHTower.ChiRamanujanCriticalDistinguishedPrime

/-!
# Complete critical source at physical prime heights

The complete third critical atom source contracts the full third Fourier-lift
block to exact physical prime logarithms. It commutes with both original
contraction projectors. Finite torsion coefficient extraction proves joint
absolute summability for each individual physical-height slice, so the finite
height sum may move outside both complete tangential lift sums. The actual
Schwartz family retains its original negligible sharp/smooth edge error.
No growing signed cancellation estimate or RH proof is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff BigOperators
namespace RHTower.BAGTrace

/-- The complete third Fourier-lift block, with both tangential frequencies fixed. -/
def bagThirdLiftBlock (f : SchwartzMap BAGPhysicalSpace ℂ) (ξ υ z : ℝ) : ℂ :=
  ∑' n : ℤ, (𝓕 f) (WithLp.toLp 2 ![ξ,υ,(n : ℝ)-z])

/-- The entire finite critical source acts in the third coordinate. -/
def bagThirdCriticalSource (P : Finset ℕ) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ((ℝ × ℝ × ℝ) → ℂ) where
  toFun F x := ∑ c : RamanujanPrimeOnlyAtomIndex P,
    (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
      F (x.1,x.2.1,x.2.2+ramanujanPrimeOnlyAtomNode c)
  map_add' F G := by
    funext x
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

private lemma phase_add (n : ℤ) (x y : ℝ) :
    ramanujanFourierPhase n (x+y)=ramanujanFourierPhase n x*ramanujanFourierPhase n y := by
  simp only [ramanujanFourierPhase,← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma physical_phase (n : ℤ) (z : ℝ) :
    Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I)=ramanujanFourierPhase n z := by
  unfold ramanujanFourierPhase
  congr 1
  push_cast
  ring

/-- The distinguished multiplier retains every finite physical-height coefficient. -/
def bagPrimeHeightBlock (P : Finset ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b ξ υ z : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (⌈a⌉ : ℤ) ⌊b⌋,
    (ramanujanDistinguishedPrimeMultiplier P n.natAbs : ℂ)*
      ramanujanFourierPhase n z*bagThirdPhysicalSlice f ξ υ n

/-- Exact third-source contraction before either tangential lift is summed. -/
theorem bagThirdCriticalSource_block (P : Finset ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b : ℝ) (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0)
    (ξ υ z : ℝ) :
    (∑ c : RamanujanPrimeOnlyAtomIndex P, (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
      bagThirdLiftBlock f ξ υ (z+ramanujanPrimeOnlyAtomNode c)) =
      bagPrimeHeightBlock P f a b ξ υ z := by
  classical
  have he (w : ℝ) : bagThirdLiftBlock f ξ υ w =
      ∑ n ∈ Finset.Icc (⌈a⌉ : ℤ) ⌊b⌋,
        ramanujanFourierPhase n w*bagThirdPhysicalSlice f ξ υ n := by
    simpa only [bagThirdLiftBlock,physical_phase] using bagThirdLift_poisson_finite f a b hs ξ υ w
  simp_rw [he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold bagPrimeHeightBlock
  apply Finset.sum_congr rfl
  intro n hn
  rw [← sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished P n]
  simp only [phase_add,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  ring

private lemma full_summable (f : SchwartzMap BAGPhysicalSpace ℂ) (x y z : ℝ) :
    Summable (fun k : ℤ × ℤ × ℤ => (𝓕 f)
      (WithLp.toLp 2 ![(k.1 : ℝ)-x,(k.2.1 : ℝ)-y,(k.2.2 : ℝ)-z])) := by
  have h := (summable_norm_bagFourierIntegerTriple f (-WithLp.toLp 2 ![x,y,z])).of_norm
  apply h.congr
  intro k
  have he : bagIntegerTriple k + -WithLp.toLp 2 ![x,y,z] =
      WithLp.toLp 2 ![(k.1 : ℝ)-x,(k.2.1 : ℝ)-y,(k.2.2 : ℝ)-z] := by
    ext i
    fin_cases i <;> rfl
  exact congrArg (fun v : BAGPhysicalSpace => (𝓕 f) v) he

/-- Every full third-lift block is absolutely summable jointly in the two remaining lifts. -/
theorem summable_norm_bagThirdLiftBlockPairs (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x y z : ℝ) :
    Summable (fun k : ℤ × ℤ => ‖bagThirdLiftBlock f ((k.1 : ℝ)-x) ((k.2 : ℝ)-y) z‖) := by
  exact (((full_summable f x y z).comp_injective (Equiv.prodAssoc ℤ ℤ ℤ).injective).prod).norm

/-- Both outer sums converge for each whole third-lift block. -/
theorem summable_bagThirdLiftBlocks (f : SchwartzMap BAGPhysicalSpace ℂ) (x y z : ℝ) :
    (∀ k : ℤ, Summable (fun l : ℤ => bagThirdLiftBlock f ((k : ℝ)-x) ((l : ℝ)-y) z)) ∧
    Summable (fun k : ℤ => ∑' l : ℤ, bagThirdLiftBlock f ((k : ℝ)-x) ((l : ℝ)-y) z) := by
  have h := (summable_norm_bagThirdLiftBlockPairs f x y z).of_norm
  exact ⟨h.prod_factor,h.prod⟩

/-- Full-lattice Fubini, before applying any arithmetic source. -/
theorem bagLiftedFourierTest_eq_thirdBlocks (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x : ℝ × ℝ × ℝ) :
    bagLiftedFourierTest f x = ∑' k : ℤ, ∑' l : ℤ,
      bagThirdLiftBlock f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) x.2.2 := by
  have he (k : ℤ × ℤ × ℤ) :
      (𝓕 f) (bagIntegerTriple k-WithLp.toLp 2 ![x.1,x.2.1,x.2.2]) =
      (𝓕 f) (WithLp.toLp 2 ![(k.1 : ℝ)-x.1,(k.2.1 : ℝ)-x.2.1,(k.2.2 : ℝ)-x.2.2]) := by
    exact congrArg (fun v : BAGPhysicalSpace => (𝓕 f) v) (by
      ext i
      fin_cases i <;> rfl)
  change (∑' k : ℤ × ℤ × ℤ,
    (𝓕 f) (bagIntegerTriple k-WithLp.toLp 2 ![x.1,x.2.1,x.2.2])) = _
  simp_rw [he]
  have h := full_summable f x.1 x.2.1 x.2.2
  rw [h.tsum_prod]
  apply tsum_congr
  intro k
  exact (h.prod_factor k).tsum_prod

private lemma sum_tsum_tsum {ι : Type*} [Fintype ι] (H : ι → ℤ → ℤ → ℂ)
    (hinner : ∀ i k, Summable (H i k)) (houter : ∀ i, Summable (fun k => ∑' l, H i k l)) :
    (∑ i, ∑' k, ∑' l, H i k l) = ∑' k, ∑' l, ∑ i, H i k l := by
  rw [← Summable.tsum_finsetSum (fun i _ => houter i)]
  apply tsum_congr
  intro k
  exact (Summable.tsum_finsetSum (fun i _ => hinner i k)).symm

/-- The height sum stays inside both complete tangential lift sums. -/
def bagPrimeHeightTest (P : Finset ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b : ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  ∑' k : ℤ, ∑' l : ℤ, bagPrimeHeightBlock P f a b ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) x.2.2

/-- Every third atom and every Fourier lift are retained in the exact contraction. -/
theorem bagThirdCriticalSource_lifted (P : Finset ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b : ℝ) (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) :
    bagThirdCriticalSource P (bagLiftedFourierTest f)=bagPrimeHeightTest P f a b := by
  funext x
  change (∑ c : RamanujanPrimeOnlyAtomIndex P, (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
    bagLiftedFourierTest f (x.1,x.2.1,x.2.2+ramanujanPrimeOnlyAtomNode c)) = _
  simp_rw [bagLiftedFourierTest_eq_thirdBlocks]
  simp only [← tsum_mul_left]
  rw [sum_tsum_tsum _ (fun c k =>
    ((summable_bagThirdLiftBlocks f x.1 x.2.1 (x.2.2+ramanujanPrimeOnlyAtomNode c)).1 k).mul_left _)
      (fun c => ?_)]
  · simp only [bagPrimeHeightTest,bagThirdCriticalSource_block P f a b hs]
  · simpa only [tsum_mul_left] using
      ((summable_bagThirdLiftBlocks f x.1 x.2.1 (x.2.2+ramanujanPrimeOnlyAtomNode c)).2).mul_left
        (ramanujanCriticalPrimeAtomWeight P c : ℂ)

/-- Third atom translation commutes with every literal three-coordinate translation. -/
theorem bagThirdCriticalSource_translate (P : Finset ℕ) (F : (ℝ × ℝ × ℝ) → ℂ)
    (v : ℝ × ℝ × ℝ) (t : ℝ) :
    bagThirdCriticalSource P (fun x => F (ramanujanTripleTranslate v t x)) =
      fun x => bagThirdCriticalSource P F (ramanujanTripleTranslate v t x) := by
  funext x
  change (∑ c : RamanujanPrimeOnlyAtomIndex P, (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
      F (ramanujanTripleTranslate v t (x.1,x.2.1,x.2.2+ramanujanPrimeOnlyAtomNode c))) =
    ∑ c : RamanujanPrimeOnlyAtomIndex P, (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
      F ((ramanujanTripleTranslate v t x).1,(ramanujanTripleTranslate v t x).2.1,
        (ramanujanTripleTranslate v t x).2.2+ramanujanPrimeOnlyAtomNode c)
  apply Finset.sum_congr rfl
  intro c hc
  exact congrArg (fun z : ℝ => (ramanujanCriticalPrimeAtomWeight P c : ℂ)*
    F (x.1+t*v.1,x.2.1+t*v.2.1,z)) (by
      dsimp only [ramanujanTripleTranslate]
      ring)

/-- Both finite averages commute with the complete third source, at every denominator. -/
theorem bagThirdCriticalSource_average (P : Finset ℕ) (D : ℕ) (v : ℝ × ℝ × ℝ)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    bagThirdCriticalSource P (ramanujanTranslationAverage D v F)=
      ramanujanTranslationAverage D v (bagThirdCriticalSource P F) := by
  have he (G : (ℝ × ℝ × ℝ) → ℂ) : ramanujanTranslationAverage D v G =
      (D : ℂ)⁻¹ • ∑ u : Fin D, (fun x => G (ramanujanTripleTranslate v ((u.val : ℝ)/D) x)) := by
    funext x
    simp only [ramanujanTranslationAverage,LinearMap.coe_mk,AddHom.coe_mk,
      Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  simp only [he,map_smul,map_sum,bagThirdCriticalSource_translate]

/-- The entire noncontracting projector commutes with the literal third source. -/
theorem bagThirdCriticalSource_projector (P : Finset ℕ) (D : ℕ)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    bagThirdCriticalSource P (ramanujanNoncontractingProjector D F)=
      ramanujanNoncontractingProjector D (bagThirdCriticalSource P F) := by
  simp only [ramanujanNoncontractingProjector,LinearMap.comp_apply,
    LinearMap.sub_apply,LinearMap.id_apply,map_sub,ramanujanContract13,ramanujanContract23,
    bagThirdCriticalSource_average]

/-- First and second literal atoms remain after the exact third-source contraction. -/
def bagCriticalPairAction (P : Finset ℕ) : ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ℂ where
  toFun F := ∑ a : RamanujanPrimeOnlyAtomIndex P, ∑ b : RamanujanPrimeOnlyAtomIndex P,
    (ramanujanCriticalPrimeAtomWeight P a : ℂ)*(ramanujanCriticalPrimeAtomWeight P b : ℂ)*
      F (ramanujanPrimeOnlyAtomNode a,ramanujanPrimeOnlyAtomNode b,0)
  map_add' F G := by
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring

theorem ramanujanCriticalTripleAtomAction_eq_pair (P : Finset ℕ)
    (F : (ℝ × ℝ × ℝ) → ℂ) :
    ramanujanCriticalTripleAtomAction P F = bagCriticalPairAction P (bagThirdCriticalSource P F) := by
  classical
  change (∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
    (ramanujanCriticalTripleAtomWeight P a : ℂ)*F (ramanujanTriplePrimeOnlyAtomNode a)) = _
  simp only [bagCriticalPairAction,bagThirdCriticalSource,LinearMap.coe_mk,AddHom.coe_mk,
    Fintype.sum_prod_type,ramanujanCriticalTripleAtomWeight,ramanujanTriplePrimeOnlyAtomNode,
    Complex.ofReal_mul,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro g hg
  ring

/-- Complete prime-height action retaining both original contraction projectors. -/
def bagPrimeHeightAction (P : Finset ℕ) (D : ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b : ℝ) : ℂ :=
  bagCriticalPairAction P (ramanujanNoncontractingProjector D (bagPrimeHeightTest P f a b))

theorem bagPrimeHeightAction_eq (P : Finset ℕ) (D : ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a b : ℝ) (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc a b → f v=0) :
    bagPrimeHeightAction P D f a b=
      ramanujanCriticalTripleAtomAction P (ramanujanNoncontractingProjector D (bagLiftedFourierTest f)) := by
  rw [ramanujanCriticalTripleAtomAction_eq_pair,bagThirdCriticalSource_projector,
    bagThirdCriticalSource_lifted P f a b hs]
  rfl

private lemma prime_multiplier_range (M : ℕ) {n : ℕ} (hn : 1 < n) (hnM : n ≤ M) :
    ramanujanDistinguishedPrimeMultiplier (Finset.range (M+1)) n =
      if n.Prime then Real.log n else 0 := by
  apply Complex.ofReal_injective
  have h := (sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished
    (Finset.range (M+1)) (n : ℤ)).symm.trans
      (sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hn hnM)
  simpa only [Int.natAbs_natCast] using h

private lemma band_natAbs {N : ℝ} (hN : 1 < N) {n : ℤ}
    (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) : 1 < n.natAbs ∧ n.natAbs ≤ ⌊2*N⌋₊ := by
  have hnr : (n : ℝ) ∈ Icc N (2*N) := by
    simpa only [Finset.mem_Icc,Int.ceil_le,Int.le_floor,Set.mem_Icc] using hn
  have hn0 : 0 ≤ n := by exact_mod_cast (le_trans (by linarith : (0 : ℝ) ≤ N) hnr.1)
  have heZ : (n.natAbs : ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hn0]
  have heR : (n.natAbs : ℝ)=(n : ℝ) := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by rw [Int.cast_natCast]
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) heZ
  constructor
  · have h : (1 : ℝ)<(n.natAbs : ℝ) := by rw [heR]; exact hN.trans_le hnr.1
    exact_mod_cast h
  · exact Nat.le_floor (heR ▸ hnr.2)

/-- On the complete positive physical band, the third multiplier selects primes exactly. -/
theorem bagPrimeHeightBlock_physical {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (ξ υ z : ℝ) :
    bagPrimeHeightBlock (Finset.range (⌊2*N⌋₊+1)) f N (2*N) ξ υ z =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ)*
          ramanujanFourierPhase n z*bagThirdPhysicalSlice f ξ υ n := by
  unfold bagPrimeHeightBlock
  apply Finset.sum_congr rfl
  intro n hn
  rw [prime_multiplier_range _ (band_natAbs hN hn).1 (band_natAbs hN hn).2]

/-- Full remaining profile at actual prime physical heights. -/
def bagPhysicalPrimeHeightTest (N : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x : ℝ × ℝ × ℝ) : ℂ :=
  ∑' k : ℤ, ∑' l : ℤ, ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
    ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ)*
      ramanujanFourierPhase n x.2.2*bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n

theorem bagPrimeHeightTest_physical {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    bagPrimeHeightTest (Finset.range (⌊2*N⌋₊+1)) f N (2*N)=bagPhysicalPrimeHeightTest N f := by
  funext x
  simp only [bagPrimeHeightTest,bagPrimeHeightBlock_physical hN,bagPhysicalPrimeHeightTest]

/-- Both original projectors and the complete first/second critical source remain. -/
def bagPhysicalPrimeHeightAction (N : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  bagCriticalPairAction (Finset.range (⌊2*N⌋₊+1))
    (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (bagPhysicalPrimeHeightTest N f))


private lemma phase_neg_mul (n r : ℤ) (z : ℝ) :
    ramanujanFourierPhase (-r) z*ramanujanFourierPhase n z=
      ramanujanFourierPhase (n-r) z := by
  simp only [ramanujanFourierPhase,← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma band_int_nonneg {N : ℝ} (hN : 1 < N) {n : ℤ}
    (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) : 0 ≤ n := by
  have hnr : N ≤ (n : ℝ) := Int.ceil_le.mp (Finset.mem_Icc.mp hn).1
  exact_mod_cast (le_trans (by linarith : (0 : ℝ) ≤ N) hnr)

private lemma band_no_alias {N : ℝ} (hN : 1 < N) {n r : ℤ}
    (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋)
    (hr : r ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) :
    ⌊2*N⌋₊+1 ∣ (n-r).natAbs ↔ n=r := by
  have hen : (n.natAbs : ℤ)=n := by
    rw [Int.natCast_natAbs,abs_of_nonneg (band_int_nonneg hN hn)]
  have her : (r.natAbs : ℤ)=r := by
    rw [Int.natCast_natAbs,abs_of_nonneg (band_int_nonneg hN hr)]
  have hb : (n-r).natAbs < ⌊2*N⌋₊+1 := by
    rw [← hen,← her]
    exact Int.natAbs_coe_sub_coe_lt_of_lt
      (Nat.lt_succ_of_le (band_natAbs hN hn).2)
      (Nat.lt_succ_of_le (band_natAbs hN hr).2)
  constructor
  · intro h
    exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt h hb))
  · rintro rfl
    simp

/-- Every physical height is an exact finite Fourier coefficient of full lift blocks. -/
theorem bagThirdPhysicalSlice_eq_torsion {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0)
    {r : ℤ} (hr : r ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) (ξ υ : ℝ) :
    bagThirdPhysicalSlice f ξ υ r = (⌊2*N⌋₊+1 : ℂ)⁻¹*
      ∑ u : Fin (⌊2*N⌋₊+1), ramanujanFourierPhase (-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))*
        bagThirdLiftBlock f ξ υ ((u.val : ℝ)/(⌊2*N⌋₊+1)) := by
  classical
  have he (z : ℝ) : bagThirdLiftBlock f ξ υ z =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        ramanujanFourierPhase n z*bagThirdPhysicalSlice f ξ υ n := by
    simpa only [bagThirdLiftBlock,physical_phase] using bagThirdLift_poisson_finite f N (2*N) hs ξ υ z
  have hu (n : ℤ) (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) :
      (∑ u : Fin (⌊2*N⌋₊+1), ramanujanFourierPhase (-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))*
        (ramanujanFourierPhase n ((u.val : ℝ)/(⌊2*N⌋₊+1))*bagThirdPhysicalSlice f ξ υ n)) =
      if n=r then (⌊2*N⌋₊+1 : ℂ)*bagThirdPhysicalSlice f ξ υ n else 0 := by
    simp only [← mul_assoc,phase_neg_mul,← Finset.sum_mul]
    have horth : (∑ u : Fin (⌊2*N⌋₊+1),
        ramanujanFourierPhase (n-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))) =
        if ⌊2*N⌋₊+1 ∣ (n-r).natAbs then (⌊2*N⌋₊+1 : ℂ) else 0 := by
      simpa only [Nat.cast_add,Nat.cast_one] using
        sum_ramanujanFourierPhase_torsion (d := ⌊2*N⌋₊+1) (Nat.succ_ne_zero _) (n-r)
    rw [horth]
    simp only [band_no_alias hN hn hr,ite_mul,zero_mul]
  have hsum : (∑ u : Fin (⌊2*N⌋₊+1),
      ramanujanFourierPhase (-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))*
        bagThirdLiftBlock f ξ υ ((u.val : ℝ)/(⌊2*N⌋₊+1))) =
      (⌊2*N⌋₊+1 : ℂ)*bagThirdPhysicalSlice f ξ υ r := by
    simp only [he,Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_congr rfl hu]
    simp only [Finset.sum_ite_eq',hr,if_true]
  rw [hsum]
  have hD : (⌊2*N⌋₊+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero ⌊2*N⌋₊)
  rw [← mul_assoc,inv_mul_cancel₀ hD,one_mul]

/-- Individual physical-height profiles are jointly absolutely summable in both lifts. -/
theorem summable_norm_bagThirdPhysicalSlicePairs {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0)
    {r : ℤ} (hr : r ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) (x y : ℝ) :
    Summable (fun k : ℤ × ℤ => ‖bagThirdPhysicalSlice f ((k.1 : ℝ)-x) ((k.2 : ℝ)-y) r‖) := by
  have hu (u : Fin (⌊2*N⌋₊+1)) : Summable (fun k : ℤ × ℤ =>
      ramanujanFourierPhase (-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))*
        bagThirdLiftBlock f ((k.1 : ℝ)-x) ((k.2 : ℝ)-y) ((u.val : ℝ)/(⌊2*N⌋₊+1))) :=
    (summable_norm_bagThirdLiftBlockPairs f x y _).of_norm.mul_left _
  have ht : Summable (fun k : ℤ × ℤ => (⌊2*N⌋₊+1 : ℂ)⁻¹*
      ∑ u : Fin (⌊2*N⌋₊+1), ramanujanFourierPhase (-r) ((u.val : ℝ)/(⌊2*N⌋₊+1))*
        bagThirdLiftBlock f ((k.1 : ℝ)-x) ((k.2 : ℝ)-y) ((u.val : ℝ)/(⌊2*N⌋₊+1))) :=
    (summable_sum (fun u _ => hu u)).mul_left _
  exact (ht.congr (fun k => (bagThirdPhysicalSlice_eq_torsion hN f hs hr _ _).symm)).norm

/-- One entire physical-height test, retaining both full tangential lift sums. -/
def bagPhysicalHeightTest (f : SchwartzMap BAGPhysicalSpace ℂ) (r : ℤ)
    (x : ℝ × ℝ × ℝ) : ℂ :=
  ramanujanFourierPhase r x.2.2*
    ∑' k : ℤ, ∑' l : ℤ, bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) r

/-- The finite height sum may now pass outside both complete tangential lift sums. -/
theorem bagPhysicalPrimeHeightTest_eq_heightSum {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0) :
    bagPhysicalPrimeHeightTest N f =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ) • bagPhysicalHeightTest f n := by
  funext x
  let w (n : ℤ) : ℂ := (if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ)
  have hsumm (n : ℤ) (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) :
      Summable (fun k : ℤ × ℤ => w n*ramanujanFourierPhase n x.2.2*
        bagThirdPhysicalSlice f ((k.1 : ℝ)-x.1) ((k.2 : ℝ)-x.2.1) n) :=
    (summable_norm_bagThirdPhysicalSlicePairs hN f hs hn x.1 x.2.1).of_norm.mul_left _
  change (∑' k : ℤ, ∑' l : ℤ, ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
    w n*ramanujanFourierPhase n x.2.2*bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n)=_
  have hinner (k : ℤ) :
      (∑' l : ℤ, ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        w n*ramanujanFourierPhase n x.2.2*bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n) =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋, ∑' l : ℤ,
        w n*ramanujanFourierPhase n x.2.2*bagThirdPhysicalSlice f ((k : ℝ)-x.1) ((l : ℝ)-x.2.1) n :=
    Summable.tsum_finsetSum (fun n hn => (hsumm n hn).prod_factor k)
  simp only [hinner]
  rw [Summable.tsum_finsetSum (fun n hn => (hsumm n hn).prod)]
  simp only [tsum_mul_left,bagPhysicalHeightTest,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,mul_assoc,w]

/-- Exact sum over physical prime heights with both original projectors on each whole row. -/
theorem bagPhysicalPrimeHeightAction_eq_heightSum {N : ℝ} (hN : 1 < N)
    (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0) :
    bagPhysicalPrimeHeightAction N f =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ)*
          bagCriticalPairAction (Finset.range (⌊2*N⌋₊+1))
            (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (bagPhysicalHeightTest f n)) := by
  rw [bagPhysicalPrimeHeightAction,bagPhysicalPrimeHeightTest_eq_heightSum hN f hs]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- Complete projected pair action, summed over actual physical prime heights. -/
def bagResolvedPrimeHeightAction (N : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
    ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ)*
      bagCriticalPairAction (Finset.range (⌊2*N⌋₊+1))
        (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (bagPhysicalHeightTest f n))

private lemma actual_box {N : ℝ} {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → A v=0 := by
  intro v i hi
  have hz0 : η (v i)=0 := hz _ (fun h => hi ⟨h.1.le,h.2.le⟩)
  rw [hA]
  fin_cases i <;> simp_all [bagCubicPhysicalAmplitude,bagCubicMellinSliceValue]

theorem primeGaussianCubicSmoothedOffDiagonal_eq_primeHeight {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    primeGaussianCubicSmoothedOffDiagonal N η=bagResolvedPrimeHeightAction N A := by
  have hbox := actual_box hz A hA
  change primeGaussianCubicSmoothedOffDiagonal N η =
    ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
      ((if n.natAbs.Prime then Real.log n.natAbs else 0 : ℝ) : ℂ)*
        bagCriticalPairAction (Finset.range (⌊2*N⌋₊+1))
          (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (bagPhysicalHeightTest A n))
  rw [← bagPhysicalPrimeHeightAction_eq_heightSum hN A hbox]
  rw [primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction hN.le hz A hA,
    ← bagPrimeHeightAction_eq _ _ A N (2*N) hbox]
  simp only [bagPrimeHeightAction,bagPrimeHeightTest_physical hN,bagPhysicalPrimeHeightAction]

/-- Unconditional actual family with exact prime-height action and the original edge error. -/
theorem exists_bagPhysicalPrimeHeightFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N)=bagResolvedPrimeHeightAction N (A N)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-bagResolvedPrimeHeightAction N (A N)‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalFourierFamily
  have he : ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N (η N)=bagResolvedPrimeHeightAction N (A N) := by
    filter_upwards [hA,eventually_ge_atTop (2 : ℕ)] with N hreg hN
    exact primeGaussianCubicSmoothedOffDiagonal_eq_primeHeight
      (by exact_mod_cast (by omega : 1 < N)) hreg.2.2.2.1 (A N) hreg.2.2.2.2.2.1
  refine ⟨η,A,?_,?_⟩
  · filter_upwards [hA,he] with N hreg heq
    exact ⟨hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1,hreg.2.2.2.2.1,hreg.2.2.2.2.2.1,heq⟩
  · apply herr.congr'
    filter_upwards [he] with N heq
    rw [heq]

end RHTower.BAGTrace
