import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheExactFirstSquarefreeBandwidth
import GaloisForLFunctions.HTGeometry.ParityDigitAffinityExpansion
import GaloisForLFunctions.RHTower.PrimeGapDirichletContinuation
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRootCountCircle
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Half-integer limits of the first squarefree bandwidth

The first correction to the inverse-length law records the integer age
of the last squarefree pair. Chinese remaindering creates arbitrarily
long gaps between such pairs, so all positive ages recur arbitrarily
late. Together with the quadratic term of the logarithm this determines
the whole finite cluster set.
-/
noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- Distance from the left endpoint of the last occupied pair to the cutoff. -/
def squarefreePairAge (N : ℕ) := N-lastSquarefreeNeighbor N

/-- Error in the leading inverse-length bandwidth at the next natural scale. -/
def squarefreeBandwidthCorrection (N : ℕ) :=
  (N:ℝ)^2*(firstSquarefreeBandwidth N-1/(N:ℝ))

private theorem last_atTop : Tendsto lastSquarefreeNeighbor atTop atTop := by
  refine tendsto_atTop.mpr fun B => ?_
  filter_upwards [eventually_ge_atTop (2*B+1),
    last_squarefree_neighbor_ratio.eventually_const_lt (by norm_num : (1/2:ℝ)<1)] with N hN hnear
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hnear' := (lt_div_iff₀ hn).mp hnear
  have hB : 2*(B:ℝ)≤N := by exact_mod_cast (show 2*B≤N by omega)
  exact_mod_cast (show (B:ℝ)≤lastSquarefreeNeighbor N by linarith only [hB,hnear'])

/-- Arbitrarily far out, each member of a prescribed block has a square
prime divisor. The witnessing prime can be chosen separately at each site. -/
private theorem missing_block (B H : ℕ) :
    ∃ A : ℕ,B≤A ∧ ∀ i < H,¬Squarefree (A+i) := by
  let p := _root_.RHTower.PrimeGapDirichlet.prime
  let m := fun i => p i^2
  let a := fun i => (B+i)*(m i-1)
  have hp (i : ℕ) : (p i).Prime := _root_.RHTower.PrimeGapDirichlet.prime_prime i
  have hm (i : ℕ) : 0 < m i := pow_pos (hp i).pos _
  have hc := Nat.chineseRemainderOfFinset a m (range H) (fun i _ => (hm i).ne') (by
    intro i _ j _ hij
    have hne : p i≠p j := fun h => hij (_root_.RHTower.PrimeGapDirichlet.prime_strictMono.injective h)
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr hne).pow_left 2).pow_right 2)
  refine ⟨hc.val+B,Nat.le_add_left _ _,fun i hi hsf => ?_⟩
  have hres := (hc.property i (mem_range.mpr hi)).add (Nat.ModEq.refl (B+i))
  have he : a i+(B+i)=(B+i)*m i := by
    dsimp only [a]
    rw [←Nat.mul_succ]
    congr 1
    have := hm i
    omega
  rw [he] at hres
  have hz : (B+i)*m i ≡ 0 [MOD m i] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
  have hd := Nat.modEq_zero_iff_dvd.mp (hres.trans hz)
  exact Nat.squarefree_iff_prime_squarefree.mp hsf _ (hp i)
    (by simpa only [m,pow_two,Nat.add_assoc] using hd)

/-- Each positive age occurs past every cutoff, even when it is prescribed
first and the intervening squarefree gaps have no specified location. -/
theorem squarefree_pair_age_recurrent {s : ℕ} (hs : 0<s) (B : ℕ) :
    ∃ N : ℕ,B≤N ∧ squarefreePairAge N=s := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (last_atTop.eventually_ge_atTop B)
  obtain ⟨A,hA,hempty⟩ := missing_block (max M 2) s
  have hA2 := (le_max_right M 2).trans hA
  let k := lastSquarefreeNeighbor A
  have hkB : B≤k := hM A ((le_max_left M 2).trans hA)
  obtain ⟨hk,hkA,hks,hks',hmax⟩ := last_squarefree_neighbor_spec hA2
  change k<A at hkA
  change 0<k at hk
  have hks2 : 2≤k+s := by omega
  obtain ⟨hj,hjM,hj₁,hj₂,hlast⟩ := last_squarefree_neighbor_spec hks2
  let j := lastSquarefreeNeighbor (k+s)
  have hkle : k≤j := hlast k hk (by omega) hks hks'
  have hjle : j≤k := by
    by_cases hjA : j<A
    · exact hmax j hj hjA hj₁ hj₂
    · have hsplit : A+(j-A)=j := by omega
      have hjM' : j<k+s := hjM
      have hh := hempty (j-A) (by omega)
      rw [hsplit] at hh
      exact (hh hj₁).elim
  refine ⟨k+s,by omega,?_⟩
  change k+s-j=s
  omega

private def localCorrection (k : ℕ) := (k:ℝ)^2*(adjacentLogGap k-1/(k:ℝ))

private theorem correction_limit : Tendsto localCorrection atTop (𝓝 (-(1/2:ℝ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n : ℕ => 4/(n:ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hb : |(n:ℝ)⁻¹|≤3/4 := by
    rw [abs_of_pos (inv_pos.mpr hn'),←one_div,div_le_iff₀ hn']
    have htwo : (2:ℝ)≤n := by exact_mod_cast hn
    linarith only [htwo]
  have he := GaloisForLFunctions.HTGeometry.abs_log_one_add_taylor_le hb
  have hlog : adjacentLogGap n=Real.log (1+(n:ℝ)⁻¹) := by
    rw [adjacent_as_ratio (by omega : 0<n),add_div,div_self hn'.ne',one_div]
  rw [Real.norm_eq_abs,localCorrection,hlog]
  have heq : (n:ℝ)^2*(Real.log (1+(n:ℝ)⁻¹)-1/n) - -(1/2:ℝ)=
      (n:ℝ)^2*(Real.log (1+(n:ℝ)⁻¹)-(n:ℝ)⁻¹+((n:ℝ)⁻¹)^2/2) := by
    field_simp [hn'.ne']
    ring
  rw [heq,abs_mul,abs_of_nonneg (sq_nonneg _)]
  apply (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq
  rw [abs_of_pos (inv_pos.mpr hn')]
  field_simp [hn'.ne']

private def apertureRatio (N : ℕ) := (N:ℝ)/(lastSquarefreeNeighbor N:ℝ)

private theorem aperture_limit : Tendsto apertureRatio atTop (𝓝 1) := by
  have h := last_squarefree_neighbor_ratio.inv₀ one_ne_zero
  rw [inv_one] at h
  change Tendsto (fun N : ℕ => (N:ℝ)/(lastSquarefreeNeighbor N:ℝ)) atTop (𝓝 1)
  simpa only [inv_div] using h

private theorem age_decomposition {N : ℕ} (hN : 2≤N) :
    squarefreeBandwidthCorrection N = apertureRatio N*(squarefreePairAge N:ℝ)+
      (apertureRatio N)^2*localCorrection (lastSquarefreeNeighbor N) := by
  obtain ⟨hk,hkN,_⟩ := last_squarefree_neighbor_spec hN
  have hk' : (lastSquarefreeNeighbor N:ℝ)≠0 := (Nat.cast_pos.mpr hk : 0<(lastSquarefreeNeighbor N:ℝ)).ne'
  have hn : (N:ℝ)≠0 := (Nat.cast_pos.mpr (by omega : 0<N) : 0<(N:ℝ)).ne'
  dsimp only [squarefreeBandwidthCorrection,squarefreePairAge,apertureRatio,localCorrection,firstSquarefreeBandwidth]
  rw [Nat.cast_sub hkN.le]
  field_simp [hk',hn]
  ring

private theorem limiting_age {α : Type*} {l : Filter α} {N : α → ℕ} (hN : Tendsto N l atTop) (z : ℝ) :
    Tendsto (fun i => squarefreeBandwidthCorrection (N i)) l (𝓝 z) ↔
      Tendsto (fun i => (squarefreePairAge (N i):ℝ)) l (𝓝 (z+1/2)) := by
  have hr := aperture_limit.comp hN
  have hc := (correction_limit.comp last_atTop).comp hN
  have he := (hr.pow 2).mul hc
  simp only [one_pow,one_mul] at he
  constructor
  · intro h
    have ht := (h.sub he).div hr one_ne_zero
    simp only [sub_neg_eq_add,div_one] at ht
    apply ht.congr'
    filter_upwards [hN.eventually_ge_atTop 2] with i hi
    have hp := (last_squarefree_neighbor_spec hi).1
    have ha : apertureRatio (N i)≠0 := div_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (Nat.cast_ne_zero.mpr hp.ne')
    change (squarefreeBandwidthCorrection (N i)-(apertureRatio (N i))^2*
      localCorrection (lastSquarefreeNeighbor (N i)))/apertureRatio (N i)=_
    rw [age_decomposition hi,add_sub_cancel_right,mul_div_cancel_left₀ _ ha]
  · intro h
    have ht := (hr.mul h).add he
    rw [one_mul,show z+1/2+ -(1/2:ℝ)=z by ring] at ht
    exact ht.congr' ((hN.eventually_ge_atTop 2).mono fun i hi => (age_decomposition hi).symm)

/-- A finite next-order limit occurs exactly when the age is eventually
constant. Its value is the integer age minus one half. -/
theorem squarefree_bandwidth_limit_iff_age {α : Type*} {l : Filter α} [l.NeBot]
    {N : α → ℕ} (hN : Tendsto N l atTop) (z : ℝ) :
    Tendsto (fun i => squarefreeBandwidthCorrection (N i)) l (𝓝 z) ↔
      ∃ s : ℕ,0<s ∧ z=(s:ℝ)-1/2 ∧ ∀ᶠ i in l,squarefreePairAge (N i)=s := by
  rw [limiting_age hN z]
  constructor
  · intro ht
    obtain ⟨s,hs⟩ := _root_.RiemannGaussian.eventuallyEq_nat_of_tendsto_natCast_mul
      (fun i => squarefreePairAge (N i)) (a:=1) zero_lt_one (by simpa only [mul_one] using ht)
    have he : Tendsto (fun i => (squarefreePairAge (N i):ℝ)) l (𝓝 (s:ℝ)) :=
      tendsto_const_nhds.congr' (hs.mono fun i hi => by simp only [hi])
    have hv := tendsto_nhds_unique ht he
    obtain ⟨i,hi,hb⟩ := (hs.and (hN.eventually_ge_atTop 2)).exists
    have hpos : 0<squarefreePairAge (N i) := Nat.sub_pos_of_lt (last_squarefree_neighbor_spec hb).2.1
    exact ⟨s,hi ▸ hpos,by linarith only [hv],hs⟩
  · rintro ⟨s,_,hz,hs⟩
    rw [hz,sub_add_cancel]
    exact tendsto_const_nhds.congr' (hs.mono fun i hi => by simp only [hi])

/-- The finite cluster values of N² times the error in the first bandwidth
are exactly 1/2, 3/2, 5/2, and so on. Every value occurs cofinally. -/
theorem first_squarefree_bandwidth_finite_cluster_set (z : ℝ) :
    (∃ N : ℕ → ℕ,Tendsto N atTop atTop ∧
      Tendsto (fun i => squarefreeBandwidthCorrection (N i)) atTop (𝓝 z)) ↔
      ∃ s : ℕ,0<s ∧ z=(s:ℝ)-1/2 := by
  constructor
  · rintro ⟨N,hN,hz⟩
    obtain ⟨s,hp,he,_⟩ := (squarefree_bandwidth_limit_iff_age hN z).mp hz
    exact ⟨s,hp,he⟩
  · rintro ⟨s,hs,he⟩
    choose N hbig hage using fun i => squarefree_pair_age_recurrent hs i
    have hN : Tendsto N atTop atTop := tendsto_atTop_mono hbig tendsto_id
    exact ⟨N,hN,(squarefree_bandwidth_limit_iff_age hN _).mpr ⟨s,hs,he,.of_forall hage⟩⟩

/-- There are also cutoffs along which the second-order correction grows
without bound. -/
theorem first_squarefree_bandwidth_unbounded_correction :
    ∃ N : ℕ → ℕ,Tendsto N atTop atTop ∧
      Tendsto (fun i => squarefreeBandwidthCorrection (N i)) atTop atTop := by
  choose N hbig hage using fun i => squarefree_pair_age_recurrent (s:=i+1) (Nat.succ_pos _) i
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono hbig tendsto_id
  have hr := aperture_limit.comp hN
  have he := (hr.pow 2).mul ((correction_limit.comp last_atTop).comp hN)
  rw [one_pow,one_mul] at he
  refine ⟨N,hN,tendsto_atTop.mpr fun b => ?_⟩
  filter_upwards [hN.eventually_ge_atTop 2,hr.eventually_const_lt (by norm_num : (1/2:ℝ)<1),
    he.eventually_const_lt (by norm_num : (-1:ℝ)< -(1/2:ℝ)),
    (tendsto_natCast_atTop_atTop : Tendsto (fun i : ℕ => (i:ℝ)) atTop atTop).eventually_ge_atTop (2*(b+1))]
    with i hi hir hie hib
  rw [age_decomposition hi,hage,Nat.cast_succ]
  change 1/2<apertureRatio (N i) at hir
  change -1<(apertureRatio (N i))^2*localCorrection (lastSquarefreeNeighbor (N i)) at hie
  have hlow := mul_le_mul_of_nonneg_right hir.le (show 0≤(i:ℝ)+1 by positivity)
  linarith only [hlow,hie,hib]

#print axioms squarefree_pair_age_recurrent
#print axioms squarefree_bandwidth_limit_iff_age
#print axioms first_squarefree_bandwidth_finite_cluster_set
#print axioms first_squarefree_bandwidth_unbounded_correction
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
