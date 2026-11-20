import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfAWindowIsFiniteAtEveryScale
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketMatricesAtFiniteScaleHaveAnExplicitError

/-!
# Forward harmonic vacancies in a Weil comb

Each missing site above a conductor removes a positive jet interaction.
The squared coefficients weight the resulting harmonic deficit. If the
support omits a site in every interval of fixed length, the normalized
Weil energy grows without bound on every fixed-ratio window.
-/

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
noncomputable section
open scoped Classical

/-- Reciprocal distances from n to the missing sites among its next M neighbors. -/
def forwardHarmonicHoles (S : Finset ℕ) (n M : ℕ) : ℝ :=
  ∑ m ∈ Ioc n (n+M) \ S, 1 / |(m:ℝ)-n|

private theorem row_with_holes {N M : ℕ} (hN : 0<N) {S : Finset ℕ} (hS : S⊆Ioc N (N+M))
    {n : ℕ} (hn : n∈S) :
    forwardHarmonicHoles S n M / 2 + ∑ m ∈ S.erase n, jetKernel m n ≤
      harm (2*M) + ((2*M:ℕ):ℝ)/(4*N) := by
  let V := Ioc n (n+M) \ S
  let T := Ioc N (N+2*M)
  have hloc := mem_Ioc.mp (hS hn)
  have hsub : V∪S.erase n ⊆ T.erase n := by
    intro m hm
    rcases mem_union.mp hm with h|h
    · have hh := mem_Ioc.mp (mem_sdiff.mp h).1
      exact mem_erase.mpr ⟨hh.1.ne',mem_Ioc.mpr (by omega)⟩
    · have hh := mem_Ioc.mp (hS (mem_of_mem_erase h))
      exact mem_erase.mpr ⟨ne_of_mem_erase h,mem_Ioc.mpr (by omega)⟩
  have hd : Disjoint V (S.erase n) :=
    disjoint_left.mpr fun _ hv hs => (mem_sdiff.mp hv).2 (mem_of_mem_erase hs)
  have hjet := sum_jetKernel_erase_le hN (S:=T) Subset.rfl
    (show n∈T from mem_Ioc.mpr (by omega))
  have hsum := (sum_le_sum_of_subset_of_nonneg (f:=fun m => jetKernel m n) hsub
    (fun m _ _ => jetKernel_nonneg m n)).trans hjet
  rw [sum_union hd] at hsum
  apply le_trans (add_le_add_right _ _) hsum
  change (∑ m ∈ V, 1/|(m:ℝ)-n|)/2 ≤ _
  rw [sum_div]
  exact sum_le_sum fun m _ => by
    unfold jetKernel
    linarith only [(by positivity : (0:ℝ)≤1/((m:ℝ)+n))]

/-- The aperture loss bounds the full regular jet, prime contacts and pole plane. -/
def combHoleLoss (Q : ℕ) : ℝ :=
  1 + Real.log (2*(Q:ℝ)) + Real.log (2*Real.pi) + (Q:ℝ)/2 +
    2*chebyshev (Q+1) + (Q:ℝ)^3/2

/-- A weighted harmonic sum over actual holes lower-bounds the energy of
every signed profile. The base scale disappears from the loss. -/
theorem combForm_forward_holes_floor {Q N : ℕ} (hQ : 0<Q) (hN : 0<N)
    {S : Finset ℕ} (hS : S⊆Ioc N (N+Q*N)) (c : ℕ → ℝ) :
    (∑ n ∈ S, (c n)^2*forwardHarmonicHoles S n (Q*N))/2 -
      combHoleLoss Q * ∑ n ∈ S,(c n)^2 ≤ combForm S c := by
  let C := combHoleLoss Q-(Q:ℝ)^3/2
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hQ' : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have har := harm_le_one_add_log (2*(Q*N))
  rw [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_mul,← mul_assoc,Real.log_mul (by positivity) hN'.ne'] at har
  have hreg : ((2*(Q*N):ℕ):ℝ)/(4*N) = (Q:ℝ)/2 := by push_cast; field_simp [hN'.ne'] <;> ring
  have hrow (n : ℕ) (hn : n∈S) :
      forwardHarmonicHoles S n (Q*N)/2 + combPotential S n ≤ C := by
    have hjet := row_with_holes hN hS hn
    rw [hreg] at hjet
    have hc := sum_contact_erase_le hN (Q:=Q+1) (by rw [Nat.succ_mul,Nat.add_comm]) hS hn
    have hct : counterterm N≤counterterm n :=
      Real.log_le_log (div_pos hN' (by positivity))
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr (mem_Ioc.mp (hS hn)).1.le) (by positivity))
    rw [counterterm,Real.log_div hN'.ne' (by positivity)] at hct
    simp only [combPotential,pairKernel,sum_add_distrib,C,combHoleLoss]
    linarith only [hjet,hc,har,hct]
  have hsum := sum_le_sum (s:=S) fun n hn =>
    mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg (c n))
  simp only [mul_add,← mul_div_assoc,sum_add_distrib,← sum_div,← sum_mul] at hsum
  have hpole := neg_le_two_mul_degOne_mul_degTwo hN hS c
  have he : ((Q*N:ℕ):ℝ)^3/(2*(N:ℝ)^3)=(Q:ℝ)^3/2 := by
    rw [Nat.cast_mul,mul_pow]
    field_simp [hN'.ne'] <;> ring
  rw [he] at hpole
  rw [HodgeTheoryOfAFixedPart.combForm,combPairing_eq_potential_sub_dirichlet]
  dsimp only [C] at hsum
  linarith only [hsum,hpole,combDirichlet_nonneg S c]

/-- With one hole in each consecutive r-block, the first K disjoint
blocks above every n contribute at least H_K/r. -/
theorem harmonic_holes_of_no_run {r M K : ℕ} (hr : 0<r) (hK : K*r≤M)
    (S : Finset ℕ) (hgap : ∀ a : ℕ, ∃ m∈Ioc a (a+r), m∉S) (n : ℕ) :
    harm K/(r:ℝ) ≤ forwardHarmonicHoles S n M := by
  choose w hmem hout using hgap
  let f (j : ℕ) := w (n+j*r)
  have bounds (j : ℕ) : n+j*r < f j ∧ f j ≤ n+(j+1)*r := by
    simpa only [Nat.succ_mul,Nat.add_assoc] using mem_Ioc.mp (hmem (n+j*r))
  have hmono : StrictMono f := by
    intro i j hij
    have hh := Nat.mul_le_mul_right r (show i+1≤j from hij)
    exact (bounds i).2.trans_lt ((Nat.add_le_add_left hh n).trans_lt (bounds j).1)
  have hsub : (range K).image f ⊆ Ioc n (n+M) \ S := by
    intro m hm
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
    have hh := (Nat.mul_le_mul_right r (show j+1≤K from mem_range.mp hj)).trans hK
    exact mem_sdiff.mpr ⟨mem_Ioc.mpr ⟨(Nat.le_add_right n _).trans_lt (bounds j).1,
      (bounds j).2.trans (Nat.add_le_add_left hh _)⟩,hout _⟩
  calc
    harm K/(r:ℝ) ≤ ∑ j ∈ range K, 1/|(f j:ℝ)-n| := by
      rw [harm,sum_div]
      refine sum_le_sum fun j _ => ?_
      have hlow : (n:ℝ)<f j := Nat.cast_lt.mpr ((Nat.le_add_right n _).trans_lt (bounds j).1)
      have hhigh : (f j:ℝ)≤(n:ℝ)+((j:ℝ)+1)*r := by exact_mod_cast (bounds j).2
      rw [abs_of_pos (sub_pos.mpr hlow),div_div]
      exact one_div_le_one_div_of_le (sub_pos.mpr hlow) (by linarith only [hhigh])
    _ = ∑ m ∈ (range K).image f, 1/|(m:ℝ)-n| := (sum_image hmono.injective.injOn).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)

/-- Finite-scale logarithmic penalty for support with no full r-block.
There are floor(QN/r) disjoint chances to see a hole above each row. -/
theorem combForm_no_run_floor {N Q r : ℕ} (hN : 0<N) (hQ : 0<Q) (hr : 0<r)
    {S : Finset ℕ} (hS : S⊆Ioc N (N+Q*N)) (hgap : ∀ a : ℕ, ∃ m∈Ioc a (a+r), m∉S)
    (c : ℕ → ℝ) :
    (harm (Q*N/r)/(2*(r:ℝ)) - combHoleLoss Q)*(∑ n ∈ S, (c n)^2) ≤ combForm S c := by
  let K := Q*N/r
  have hK : K*r≤Q*N := Nat.div_mul_le_self _ _
  have hh := sum_le_sum (s:=S) fun n _ =>
    mul_le_mul_of_nonneg_left (harmonic_holes_of_no_run hr hK S hgap n) (sq_nonneg (c n))
  rw [← sum_mul] at hh
  have hhalf := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)
  have he : (∑ n ∈ S, (c n)^2)*(harm K/r)/2 =
      (harm K/(2*(r:ℝ)))*(∑ n ∈ S,(c n)^2) := by ring
  rw [he] at hhalf
  change (harm K/(2*(r:ℝ)) - combHoleLoss Q)*(∑ n ∈ S, (c n)^2) ≤ _
  linarith only [hhalf,combForm_forward_holes_floor hQ hN hS c]

/-- A low reading on a support without an r-run forces
log(1+floor(QN/r)) < 2r(B+loss). Thus the longest occupied run
must grow at least logarithmically with the base scale. -/
theorem low_energy_no_run_scale_bound {N Q r : ℕ} (hN : 0<N) (hQ : 0<Q) (hr : 0<r)
    {S : Finset ℕ} (hS : S⊆Ioc N (N+Q*N)) (hgap : ∀ a : ℕ, ∃ m∈Ioc a (a+r), m∉S)
    (c : ℕ → ℝ) (B : ℝ) (hlow : combForm S c < B*∑ n ∈ S, (c n)^2) :
    Real.log (((Q*N/r:ℕ):ℝ)+1) < 2*(r:ℝ)*(B+combHoleLoss Q) := by
  let K := Q*N/r
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have h := (combForm_no_run_floor hN hQ hr hS hgap c).trans_lt hlow
  have hmass : 0≤∑ n ∈ S, (c n)^2 := sum_nonneg fun _ _ => sq_nonneg _
  have hsmall : harm K/(2*(r:ℝ))-combHoleLoss Q < B := by
    by_contra! he
    exact h.not_ge (mul_le_mul_of_nonneg_right he hmass)
  have hh : harm K/(2*(r:ℝ)) < B+combHoleLoss Q := by linarith only [hsmall]
  have hlog : Real.log ((K:ℝ)+1) ≤ harm K := by
    rw [harm_eq_harmonic]
    simpa only [Nat.cast_add,Nat.cast_one] using log_add_one_le_harmonic K
  linarith only [hlog,(div_lt_iff₀ (by positivity : (0:ℝ)<2*r)).mp hh]

/-- Omitting a site in every run of fixed length eventually gives any
prescribed normalized energy floor, for arbitrary signed coefficients. -/
theorem eventually_comb_floor_of_no_run {Q r : ℕ} (hQ : 0<Q) (hr : 0<r) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ), S⊆Ioc N (N+Q*N) →
      (∀ a : ℕ, ∃ m∈Ioc a (a+r), m∉S) →
      ∀ c : ℕ → ℝ, B*(∑ n ∈ S, (c n)^2) ≤ combForm S c := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK,hpos⟩ := ((hlog.eventually_ge_atTop
    (2*(B+combHoleLoss Q)*r-Real.eulerMascheroniConstant)).and (eventually_ge_atTop 1)).exists
  change _ ≤ Real.log (K:ℝ) at hK
  have hk : 2*(B+combHoleLoss Q) ≤ harm K/(r:ℝ) := (le_div_iff₀ hr').mpr
    (by linarith only [hK,(harm_sub_log_sub_gamma_mem hpos).1])
  filter_upwards [eventually_ge_atTop (max 1 (K*r))] with N hN
  have hn : 0<N := (le_max_left 1 _).trans hN
  have hM : K*r≤Q*N := ((le_max_right 1 _).trans hN).trans (Nat.le_mul_of_pos_left N hQ)
  intro S hs hgap c
  have hidx : K ≤ Q*N/r := (Nat.le_div_iff_mul_le hr).mpr hM
  have hmono : harm K ≤ harm (Q*N/r) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hidx) (fun i _ _ => by positivity)
  have hbound : B ≤ harm (Q*N/r)/(2*(r:ℝ))-combHoleLoss Q := by
    have hraw := (le_div_iff₀ hr').mp hk
    have hh : B+combHoleLoss Q ≤ harm (Q*N/r)/(2*(r:ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [hraw,hmono])
    linarith only [hh]
  exact (mul_le_mul_of_nonneg_right hbound (sum_nonneg fun n (_ : n∈S) => sq_nonneg (c n))).trans
    (combForm_no_run_floor hn hQ hr hs hgap c)

/-- Every sufficiently late low-energy profile has an entire interval
of r consecutive nonzero coefficients, for any fixed r. -/
theorem low_Weil_energy_forces_nonzero_runs {Q r : ℕ} (hQ : 0<Q) (hr : 0<r) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ), S⊆Ioc N (N+Q*N) →
      ∀ c : ℕ → ℝ, combForm S c < B*∑ n ∈ S,(c n)^2 →
        ∃ a : ℕ, Ioc a (a+r) ⊆ S.filter (fun n => c n≠0) := by
  filter_upwards [eventually_comb_floor_of_no_run hQ hr B] with N hN S hs c hlow
  let T := S.filter (fun n => c n≠0)
  have hsub : T ⊆ S := filter_subset _ _
  have hz (n : ℕ) (hn : n∈S) (h : n∉T) : c n=0 := by
    by_contra hnz
    exact h (mem_filter.mpr ⟨hn,hnz⟩)
  by_contra hrun
  have hgap (a : ℕ) : ∃ m∈Ioc a (a+r), m∉T := by
    by_contra! he
    exact hrun ⟨a,he⟩
  have hE : ∑ n ∈ T, (c n)^2 = ∑ n ∈ S, (c n)^2 :=
    sum_subset hsub fun n hn ht => by rw [hz n hn ht,zero_pow (by decide : 2≠0)]
  rw [combForm_of_subset hsub hz,← hE] at hlow
  exact hlow.not_ge (hN T (hsub.trans hs) hgap c)

#print axioms combForm_forward_holes_floor
#print axioms combForm_no_run_floor
#print axioms low_energy_no_run_scale_bound
#print axioms harmonic_holes_of_no_run
#print axioms eventually_comb_floor_of_no_run
#print axioms low_Weil_energy_forces_nonzero_runs
end
end GaloisForLFunctions.SignedArithmeticCorrespondences
