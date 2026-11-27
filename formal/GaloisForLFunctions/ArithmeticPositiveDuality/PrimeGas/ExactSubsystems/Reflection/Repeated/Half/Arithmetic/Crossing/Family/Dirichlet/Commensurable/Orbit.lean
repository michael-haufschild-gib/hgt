import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Separation

/-! # Exact thermal observations throughout a positive rational orbit -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Set Finset
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- A single asymmetric spectrum realizes any prescribed finite collection of
positive rational multiples and rejects every other order on the same orbit. -/
theorem exact_orbit {t : ℝ} (ht : 0<t) (res : Resonant t) (T : Finset ℚ)
    (pos : ∀ q ∈ T, 0<q) :
    ∃ S, Attainable S ∧ ∀ q : ℚ, 0<q → ((q : ℝ)*t ∈ S ↔ q ∈ T) := by
  classical
  let f (q : ℚ) := (q : ℝ)*t
  let U := T.image f
  have good (s : ℝ) (hs : s ∈ U) : 0<s ∧ Resonant s := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hs
    exact ⟨mul_pos (Rat.cast_pos.mpr (pos q hq)) ht,(resonant_rational_iff ht q (pos q hq)).mpr res⟩
  refine ⟨_,least_schedule U good,fun q hq => ?_⟩
  change (f q ∈ ⋃ s ∈ U, consequences s) ↔ q ∈ T
  constructor
  · intro hit
    obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hit
    obtain ⟨mem,forced⟩ := Set.mem_iUnion.mp hs
    obtain ⟨r,hr,rfl⟩ := mem_image.mp mem
    have rp := pos r hr
    have ratio := div_pos hq rp
    have scale : ((q/r : ℚ) : ℝ)*f r=f q := by
      simp only [f,Rat.cast_div]
      field_simp [(Rat.cast_pos.mpr rp : (0 : ℝ)<r).ne']
    have force : Forces (f r) (((q/r : ℚ) : ℝ)*f r) := by
      rw [scale]
      exact forced.2
    have info := good (f r) (mem_image_of_mem f hr)
    have one := ((rational_forces_iff info.1 (q/r) ratio).mp force).resolve_right (not_not.mpr info.2)
    rwa [(div_eq_one_iff_eq rp.ne').mp one]
  · intro mem
    exact Set.mem_iUnion.mpr ⟨f q,Set.mem_iUnion.mpr ⟨mem_image_of_mem f mem,
      mul_pos (Rat.cast_pos.mpr hq) ht,fun _ _ hit => hit⟩⟩

/-- All orders on one rational orbit can be prescribed on one nonreflecting
Gibbs spectrum iff damping is nonzero and every requested pass is resonant.
At zero damping every order passes. -/
theorem rational_gibbs_iff (s : ℂ) {u : ℝ} (hu : 0<u) (T : Finset ℚ) (pos : ∀ q ∈ T, 0<q) :
    (∃ (n : ℕ) (a : Fin n → ℕ+), ¬Reflects (energy ∘ a) ∧
      ∀ q : ℚ, 0<q → (lawOrder (finiteGibbsStateWeight (2*s.re-1) (energy ∘ a)) ((q : ℝ)*u) ↔ q ∈ T)) ↔
    s.re ≠ 1/2 ∧ (T=∅ ∨ Resonant (u*|2*s.re-1|)) := by
  classical
  let d := 2*s.re-1
  let t := u*|d|
  have mid : d=0 ↔ s.re=1/2 := by dsimp only [d]; constructor <;> intro h <;> linarith only [h]
  have law {n : ℕ} (a : Fin n → ℕ+) (q : ℚ) (hq : 0<q) :
      lawOrder (finiteGibbsStateWeight d (energy ∘ a)) ((q : ℝ)*u) ↔ agrees (energy ∘ a) ((q : ℝ)*t) := by
    rw [gibbs_order,← agrees_abs _ (((q : ℝ)*u)*d),abs_mul,abs_of_pos (mul_pos (Rat.cast_pos.mpr hq) hu),mul_assoc]
  constructor
  · rintro ⟨n,a,asym,obs⟩
    have nd : d ≠ 0 := by
      intro zero
      obtain ⟨q,hq,absent⟩ := Set.Infinite.exists_notMem_finset (Set.Ioi_infinite (0 : ℚ)) T
      apply absent
      apply (obs q hq).mp
      rw [law a q hq,show t=0 by simp [t,zero],mul_zero]
      simp only [agrees,neg_zero]
    have ht : 0<t := mul_pos hu (abs_pos.mpr nd)
    refine ⟨fun h => nd (mid.mpr h),?_⟩
    rcases T.eq_empty_or_nonempty with empty | ⟨q,hq⟩
    · exact Or.inl empty
    · apply Or.inr
      apply (resonant_rational_iff ht q (pos q hq)).mp
      apply (contains_resonant (mul_pos (Rat.cast_pos.mpr (pos q hq)) ht)).mp
      exact ⟨_,⟨n,a,asym,rfl⟩,mul_pos (Rat.cast_pos.mpr (pos q hq)) ht,
        (law a q (pos q hq)).mp ((obs q (pos q hq)).mpr hq),asym⟩
  · rintro ⟨off,possible⟩
    have ht : 0<t := mul_pos hu (abs_pos.mpr (fun h => off (mid.mp h)))
    have spec : ∃ S, Attainable S ∧ ∀ q : ℚ, 0<q → ((q : ℝ)*t ∈ S ↔ q ∈ T) := by
      rcases possible with rfl | res
      · exact ⟨∅,attainable_empty,fun _ _ => by simp⟩
      · exact exact_orbit ht res T pos
    obtain ⟨_,⟨n,a,asym,rfl⟩,obs⟩ := spec
    refine ⟨n,a,asym,fun q hq => ?_⟩
    rw [law a q hq,← obs q hq]
    exact ⟨fun h => ⟨mul_pos (Rat.cast_pos.mpr hq) ht,h,asym⟩,fun h => h.2.1⟩

/-- At each rational dilation one physical spectrum realizes the uniform
exclusion of the whole upper half-line of orders. -/
theorem uniform_spectra {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℚ, 0<q → ∃ S, Attainable S ∧ (q : ℝ)*t ∈ S ∧
      ∀ r ≥ C, r*((q : ℝ)*t) ∉ S := by
  obtain ⟨C,hC,limit⟩ := uniform_forced_bound ht res
  refine ⟨C,hC,fun q hq => ?_⟩
  have src := mul_pos (Rat.cast_pos.mpr hq : (0 : ℝ)<q) ht
  exact ⟨consequences ((q : ℝ)*t),least_spectrum src ((resonant_rational_iff ht q hq).mpr res),
    ⟨src,fun _ _ h => h⟩,fun r hr hit => hr.not_gt (limit q hq r (hC.trans_le hr) hit.2)⟩

#print axioms uniform_spectra
#print axioms exact_orbit
#print axioms rational_gibbs_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
