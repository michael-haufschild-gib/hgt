import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfAWindowIsFiniteAtEveryScale

/-!
# Effective support of a low-energy Weil comb

Only nearby sites contribute to the logarithmic singularity of the jet
kernel. A spatial cutoff pays nearby interactions with a harmonic row
bound and distant interactions with the squared sum of absolute
coefficients. The resulting lower bound forces every negative profile
on a fixed-ratio interval to have macroscopic effective support.
-/

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
noncomputable section
open scoped Classical

private def nearSingularity (h m n : ℕ) : ℝ :=
  if m ≤ n+h ∧ n ≤ m+h then 1/|(m:ℝ)-n| else 0

private def nearKernel (h m n : ℕ) : ℝ := contact m n + nearSingularity h m n/2

private theorem nearKernel_comm (h m n : ℕ) : nearKernel h m n=nearKernel h n m := by
  unfold nearKernel nearSingularity
  rw [contact_comm m n,abs_sub_comm (m:ℝ) n]
  by_cases hc : m ≤ n+h ∧ n ≤ m+h
  · rw [if_pos hc,if_pos (And.intro hc.2 hc.1)]
  · have hs : ¬(n ≤ m+h ∧ m ≤ n+h) := fun h => hc ⟨h.2,h.1⟩
    rw [if_neg hc,if_neg hs]

private theorem nearKernel_nonneg (h m n : ℕ) : 0 ≤ nearKernel h m n := by
  apply add_nonneg (contact_nonneg _ _)
  unfold nearSingularity
  split_ifs <;> positivity

private theorem near_singular_row (S : Finset ℕ) (pos : ∀ m∈S, 0 < m) {n : ℕ} (hn : n∈S) (h : ℕ) :
    ∑ m ∈ S.erase n, nearSingularity h m n ≤ 2*harm (2*h+1) := by
  let T := S.filter (fun m => m ≤ n+h ∧ n ≤ m+h)
  let A := n-h-1
  have hsub : T ⊆ Ioc A (A+(2*h+1)) := by
    intro m hm
    obtain ⟨hm,hl,hr⟩ := mem_filter.mp hm
    have hpos := pos m hm
    apply mem_Ioc.mpr
    dsimp only [A]
    omega
  have hnT : n∈T := mem_filter.mpr ⟨hn,by omega⟩
  simp only [nearSingularity,← sum_filter,filter_erase]
  exact sum_inv_abs_sub_erase_le hsub hnT

private theorem pair_near_far {N h m n : ℕ} (hN : 0<N) (hh : 0<h) (hm : N < m) (hn : N < n) :
    pairKernel m n ≤ nearKernel h m n + (1/(2*(h:ℝ)) + 1/(4*(N:ℝ))) := by
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hh' : (0:ℝ)<h := Nat.cast_pos.mpr hh
  have hm' : (N:ℝ) < m := Nat.cast_lt.mpr hm
  have hn' : (N:ℝ) < n := Nat.cast_lt.mpr hn
  have hreg := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2*N)
    (show 2*(N:ℝ) ≤ (m:ℝ)+n by linarith only [hm',hn'])
  have e₁ : (1:ℝ)/(2*N)/2=1/(4*N) := by ring
  have e₂ : (1:ℝ)/h/2=1/(2*h) := by ring
  rw [pairKernel,jetKernel,nearKernel,nearSingularity,←e₁,←e₂]
  by_cases hc : m ≤ n+h ∧ n ≤ m+h
  · rw [if_pos hc]
    linarith only [hreg,(by positivity : (0:ℝ) ≤ 1/h)]
  · rw [if_neg hc,zero_div,add_zero]
    have hsep : (h:ℝ)≤|(m:ℝ)-n| := by
      rcases (show n+h < m ∨ m+h < n by omega) with he|he
      · have ht : (n:ℝ)+h < m := by exact_mod_cast he
        exact (show (h:ℝ) ≤ (m:ℝ)-n by linarith only [ht]).trans (le_abs_self _)
      · have ht : (m:ℝ)+h < n := by exact_mod_cast he
        exact (show (h:ℝ)≤-((m:ℝ)-n) by linarith only [ht]).trans (neg_le_abs _)
    linarith only [one_div_le_one_div_of_le hh' hsep,hreg]

/-- Squared Euclidean mass and total absolute mass are kept separately in
the distant interaction term. The cutoff can be chosen for each profile. -/
theorem combForm_cutoff_floor {N Q h : ℕ} (hN : 0<N) (hh : 0<h)
    {S : Finset ℕ} (hS : S⊆Ioc N (N+Q*N)) (c : ℕ → ℝ) :
    (counterterm N - harm (2*h+1) - 2*chebyshev (Q+1) - (Q:ℝ)^3/2)*
      (∑ n ∈ S, (c n)^2) -
      (1/(2*(h:ℝ))+1/(4*(N:ℝ)))*(∑ n ∈ S, |c n|)^2 ≤ combForm S c := by
  let b (n : ℕ) := |c n|
  let E := ∑ n ∈ S, (c n)^2
  let L := ∑ n ∈ S, b n
  let d := 1/(2*(h:ℝ))+1/(4*(N:ℝ))
  let K := nearKernel h
  let R := harm (2*h+1)+2*chebyshev (Q+1)
  have hd : 0≤d := by dsimp [d]; positivity
  have hx {m : ℕ} (hm : m∈S) : N < m := (mem_Ioc.mp (hS hm)).1
  have hrow {n : ℕ} (hn : n∈S) : ∑ m ∈ S.erase n, K m n ≤ R := by
    have hs := near_singular_row S (fun m hm => hN.trans (hx hm)) hn h
    have hc := sum_contact_erase_le hN (Q:=Q+1) (by rw [Nat.succ_mul,Nat.add_comm]) hS hn
    simp only [K,nearKernel,sum_add_distrib,← sum_div]
    dsimp only [R]
    linarith only [hs,hc]
  have hK : ∑ n ∈ S, ∑ m ∈ S.erase n, b m*b n*K m n ≤ R*E := by
    have bound := sum_mul_mul_le_abs_row S K (nearKernel_comm h) b
    have nonneg (m n : ℕ) : |K m n| = K m n := abs_of_nonneg (nearKernel_nonneg h m n)
    simp only [nonneg] at bound
    apply bound.trans
    rw [show R*E=∑ n ∈ S, (b n)^2*R by simp only [b,sq_abs,E,←sum_mul]; ring]
    exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow hn) (sq_nonneg _)
  have hL : ∑ n ∈ S, ∑ m ∈ S.erase n, b m*b n*d ≤ d*L^2 := by
    calc
      _ ≤ ∑ n ∈ S, ∑ m ∈ S, b m*b n*d :=
        sum_le_sum fun n _ => sum_le_sum_of_subset_of_nonneg (erase_subset n S)
          (fun m _ _ => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hd)
      _ = _ := by simp only [←sum_mul,←mul_sum,L]; ring
  have hpairs : ∑ n ∈ S, ∑ m ∈ S.erase n, c m*c n*pairKernel m n ≤ R*E+d*L^2 := by
    calc
      _ ≤ ∑ n ∈ S, ∑ m ∈ S.erase n, (b m*b n*K m n + b m*b n*d) := by
        refine sum_le_sum fun n hn => sum_le_sum fun m hm => ?_
        rw [← mul_add]
        exact mul_le_mul (by simpa only [b,abs_mul] using le_abs_self (c m*c n))
          (pair_near_far hN hh (hx (mem_of_mem_erase hm)) (hx hn)) (pairKernel_nonneg _ _)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ _ := by simp only [sum_add_distrib]; exact add_le_add hK hL
  have hdiag : counterterm N*E ≤ ∑ n ∈ S, (c n)^2*counterterm n := by
    rw [show counterterm N*E=∑ n ∈ S, (c n)^2*counterterm N by rw [← sum_mul]; ring]
    refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Real.log_le_log (by positivity : 0<(N:ℝ)/(2*Real.pi))
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hx hn).le) (by positivity))
  have hpole := neg_le_two_mul_degOne_mul_degTwo hN hS c
  have hrat : ((Q*N : ℕ):ℝ)^3/(2*(N:ℝ)^3)=(Q:ℝ)^3/2 := by
    rw [Nat.cast_mul,mul_pow]
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
  rw [hrat] at hpole
  change -((Q:ℝ)^3/2)*E ≤ _ at hpole
  change (counterterm N-harm (2*h+1)-2*chebyshev (Q+1)-(Q:ℝ)^3/2)*E-d*L^2 ≤ _
  unfold HodgeTheoryOfAFixedPart.combForm HodgeTheoryOfAFixedPart.combPairing
  dsimp only [R] at hpairs
  linarith only [hpairs,hdiag,hpole]

/-- The inverse participation ratio formed from absolute coefficients.
It equals the support size on a profile of constant absolute value. -/
def combEffectiveSupport (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ n ∈ S, |c n|)^2 / ∑ n ∈ S, (c n)^2

private theorem one_le_effectiveSupport {S : Finset ℕ} {c : ℕ → ℝ}
    (hE : 0 < ∑ n ∈ S, (c n)^2) : 1 ≤ combEffectiveSupport S c := by
  rw [combEffectiveSupport,le_div_iff₀ hE,one_mul]
  simpa only [sq_abs] using (sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun n => |c n|)
    (fun n _ => abs_nonneg _))

private def apertureLoss (Q : ℕ) : ℝ := Real.log (10*Real.pi) + 3/2 + 2*chebyshev (Q+1) + (Q:ℝ)^3/2

/-- The full Weil form gains the logarithm of ambient scale divided by
effective support. The displayed finite-scale loss retains the actual
profile dependence of the regular jet. -/
theorem combForm_effective_support_floor {N Q : ℕ} (hN : 0<N) {S : Finset ℕ}
    (hS : S⊆Ioc N (N+Q*N)) (c : ℕ → ℝ) (hE : 0<∑ n ∈ S, (c n)^2) :
    let u := combEffectiveSupport S c
    (Real.log ((N:ℝ)/u) - (Real.log (10*Real.pi)+3/2+2*chebyshev (Q+1)+(Q:ℝ)^3/2) -
      u/(4*N)) * (∑ n ∈ S, (c n)^2) ≤ combForm S c := by
  let u := combEffectiveSupport S c
  let E := ∑ n ∈ S, (c n)^2
  let L := ∑ n ∈ S, |c n|
  let h := ⌈u⌉₊
  have hu : 1≤u := one_le_effectiveSupport hE
  have hu' : 0<u := lt_of_lt_of_le zero_lt_one hu
  have hh : u≤(h:ℝ) := Nat.le_ceil u
  have hh' : (h:ℝ)<u+1 := Nat.ceil_lt_add_one hu'.le
  have hpos : 0<h := Nat.cast_pos.mp (hu'.trans_le hh)
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hL : L^2=u*E := (div_mul_cancel₀ (L^2) hE.ne').symm
  have hwidth : ((2*h+1 : ℕ) : ℝ) ≤ 5*u := by
    push_cast
    linarith only [hu,hh']
  have hwidth_pos : (0:ℝ) < ((2*h+1 : ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hlog : harm (2*h+1) ≤ 1+Real.log (5*u) := calc
    _ ≤ 1+Real.log ((2*h+1 : ℕ) : ℝ) := by
      rw [harm_eq_harmonic]
      exact_mod_cast harmonic_le_one_add_log (2*h+1)
    _ ≤ _ := add_le_add (le_refl 1) (Real.log_le_log hwidth_pos hwidth)
  have hp : u/(2*(h:ℝ)) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hh])
  have hcost : (1/(2*(h:ℝ))+1/(4*(N:ℝ)))*L^2 ≤ (1/2+u/(4*N))*E := by
    rw [hL,show (1/(2*(h:ℝ))+1/(4*(N:ℝ)))*(u*E)=(u/(2*h)+u/(4*N))*E by ring]
    exact mul_le_mul_of_nonneg_right (add_le_add hp (le_refl _)) hE.le
  have hlogid : counterterm N - (1+Real.log (5*u)) =
      Real.log ((N:ℝ)/u)-Real.log (10*Real.pi)-1 := by
    rw [counterterm,Real.log_div hN'.ne' (by positivity : 2*Real.pi≠0),Real.log_div hN'.ne' hu'.ne',
      Real.log_mul (by norm_num : (5:ℝ)≠0) hu'.ne',show 10*Real.pi=(2*Real.pi)*5 by ring,
      Real.log_mul (by positivity : 2*Real.pi≠0) (by norm_num : (5:ℝ)≠0)]
    ring
  have hc := combForm_cutoff_floor hN hpos hS c
  change (counterterm N-harm (2*h+1)-2*chebyshev (Q+1)-(Q:ℝ)^3/2)*E-_*L^2≤_ at hc
  change (_-_-u/(4*N))*E≤_
  have hlE := congrArg (fun x : ℝ => x*E) hlogid
  linarith only [mul_le_mul_of_nonneg_right hlog hE.le,hcost,hlE,hc]

/-- For each aperture and energy floor, sufficiently small effective density
forces that floor at every base scale, including on the complete comb.
Consequently a negative witness needs macroscopic absolute coefficient mass. -/
theorem low_effective_density_forces_Weil_floor (Q : ℕ) (B : ℝ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {N : ℕ}, 0<N → ∀ {S : Finset ℕ}, S⊆Ioc N (N+Q*N) →
      ∀ c : ℕ → ℝ, (∑ n ∈ S, |c n|)^2 ≤ δ*N*(∑ n ∈ S,(c n)^2) →
        B*(∑ n ∈ S, (c n)^2) ≤ combForm S c := by
  let A := |B+apertureLoss Q|+1
  let δ := Real.exp (-A)
  have hA : 0<A := by dsimp [A]; positivity
  have hδ : 0<δ := Real.exp_pos _
  have hδ₁ : δ≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA.le)
  refine ⟨δ,hδ,?_⟩
  intro N hN S hS c hsmall
  let E := ∑ n ∈ S, (c n)^2
  let L := ∑ n ∈ S, |c n|
  let u := combEffectiveSupport S c
  have hE : 0≤E := sum_nonneg fun n _ => sq_nonneg _
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  change L^2≤δ*N*E at hsmall
  change B*E ≤ _
  rcases eq_or_lt_of_le hE with hz|he
  · have hL : L^2=0 := le_antisymm (by simpa only [← hz,mul_zero] using hsmall) (sq_nonneg _)
    have hc := combForm_cutoff_floor hN (by decide : 0<1) hS c
    change _*E-_*L^2 ≤ _ at hc
    simpa only [← hz,hL,mul_zero,sub_zero] using hc
  · have hu : 0<u := lt_of_lt_of_le zero_lt_one (one_le_effectiveSupport he)
    have h₁ : u≤δ*N := (div_le_iff₀ he).mpr hsmall
    have h₂ : u≤(N:ℝ) := h₁.trans ((mul_le_mul_of_nonneg_right hδ₁ hN'.le).trans_eq (one_mul _))
    have hcancel : Real.exp A*δ=1 := by rw [show δ=Real.exp (-A) from rfl,← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have hscale : Real.exp A*u≤N := calc
      _ ≤ Real.exp A*(δ*N) := mul_le_mul_of_nonneg_left h₁ (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc,hcancel,one_mul]
    have hlog := (Real.le_log_iff_exp_le (div_pos hN' hu)).mpr ((le_div_iff₀ hu).mpr hscale)
    have hpen : u/(4*N)≤1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [h₂,hN'])
    have hb : B≤Real.log ((N:ℝ)/u)-apertureLoss Q-u/(4*N) := by
      dsimp only [A] at hlog
      linarith only [hlog,hpen,le_abs_self (B+apertureLoss Q)]
    exact (mul_le_mul_of_nonneg_right hb he.le).trans (combForm_effective_support_floor hN hS c he)

private theorem l1_squared_le (S : Finset ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ S, |c n|)^2 ≤ (S.card:ℝ)*∑ n ∈ S, (c n)^2 := by
  simpa only [one_mul,one_pow,sq_abs,sum_const,nsmul_eq_mul,mul_one] using
    sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun n => |c n|)

/-- A low-energy profile on any fixed-ratio comb must occupy a positive
fraction of the base scale. Vanishing entries are removed before counting. -/
theorem low_Weil_energy_forces_many_sites (Q : ℕ) (B : ℝ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {N : ℕ}, 0<N → ∀ {S : Finset ℕ}, S⊆Ioc N (N+Q*N) →
      ∀ c : ℕ → ℝ, combForm S c<B*(∑ n ∈ S,(c n)^2) →
        δ*N < ((S.filter fun n => c n ≠ 0).card : ℝ) := by
  obtain ⟨δ,hδ,hfloor⟩ := low_effective_density_forces_Weil_floor Q B
  refine ⟨δ,hδ,?_⟩
  intro N hN S hS c hlow
  let T := S.filter fun n => c n≠0
  have outside (n : ℕ) (hn : n∈S) (h : n∉T) : c n=0 := by
    by_contra he
    exact h (mem_filter.mpr ⟨hn,he⟩)
  have h₁ : ∑ n ∈ T, |c n| = ∑ n ∈ S, |c n| :=
    sum_subset (filter_subset _ _) fun n hn ht => by rw [outside n hn ht,abs_zero]
  have h₂ : ∑ n ∈ T, (c n)^2 = ∑ n ∈ S, (c n)^2 :=
    sum_subset (filter_subset _ _) fun n hn ht => by rw [outside n hn ht,zero_pow (by decide : 2≠0)]
  have hcs := l1_squared_le T c
  rw [h₁,h₂] at hcs
  by_contra! h
  exact hlow.not_ge (hfloor hN hS c (hcs.trans (mul_le_mul_of_nonneg_right h
    (sum_nonneg fun n _ => sq_nonneg _))))

/-- Uniform diffuseness of low-energy profiles. Removing any sufficiently
small set leaves a fixed positive fraction of their squared mass, even if
the remaining coefficients are all tiny individually. -/
theorem low_Weil_energy_has_diffuse_mass {Q : ℕ} (hQ : 0<Q) (B : ℝ) :
    ∃ δ η : ℝ, 0<δ ∧ 0<η ∧ ∀ {N : ℕ}, 0<N → ∀ {S : Finset ℕ}, S⊆Ioc N (N+Q*N) →
      ∀ c : ℕ → ℝ, combForm S c<B*(∑ n ∈ S,(c n)^2) →
      ∀ T⊆S, (T.card:ℝ)≤δ*N → η*(∑ n ∈ S,(c n)^2) < ∑ n ∈ S\T,(c n)^2 := by
  obtain ⟨α,hα,hfloor⟩ := low_effective_density_forces_Weil_floor Q B
  have hQ' : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  refine ⟨α/4,α/(4*Q),by positivity,by positivity,?_⟩
  intro N hN S hS c hlow T hT hthin
  let E := ∑ n ∈ S,(c n)^2
  let E₀ := ∑ n ∈ S\T,(c n)^2
  let L₁ := ∑ n ∈ T,|c n|
  let L₀ := ∑ n ∈ S\T,|c n|
  have hE : 0≤E := sum_nonneg fun _ _ => sq_nonneg _
  have hE₀ : 0≤E₀ := sum_nonneg fun _ _ => sq_nonneg _
  have hlarge : α*N*E < (∑ n ∈ S,|c n|)^2 := lt_of_not_ge fun h => hlow.not_ge (hfloor hN hS c h)
  have hsplit : ∑ n ∈ S, |c n| = L₀+L₁ := (sum_sdiff hT).symm
  rw [hsplit] at hlarge
  have h₁ : L₁^2≤(α/4*N)*E := (l1_squared_le T c).trans
    (mul_le_mul hthin (sum_le_sum_of_subset_of_nonneg hT (fun n _ _ => sq_nonneg _))
      (sum_nonneg fun n _ => sq_nonneg _) (by positivity))
  have hcard : (S\T).card ≤ Q*N := by
    have hh := (card_le_card (show S\T ⊆ S from sdiff_subset)).trans (card_le_card hS)
    rwa [Nat.card_Ioc,Nat.add_sub_cancel_left] at hh
  have h₀ : L₀^2≤((Q:ℝ)*N)*E₀ := (l1_squared_le (S\T) c).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE₀)
  have hraw : (N:ℝ)*(α*E)<(N:ℝ)*(4*(Q:ℝ)*E₀) := by
    nlinarith only [hlarge,h₁,h₀,sq_nonneg (L₀-L₁)]
  have hshort := (mul_lt_mul_iff_right₀ (Nat.cast_pos.mpr hN : (0:ℝ)<N)).mp hraw
  change α/(4*Q)*E<E₀
  rw [div_mul_eq_mul_div,div_lt_iff₀ (by positivity)]
  linarith only [hshort]

#print axioms low_Weil_energy_forces_many_sites
#print axioms low_Weil_energy_has_diffuse_mass

#print axioms combForm_cutoff_floor
#print axioms combForm_effective_support_floor
#print axioms low_effective_density_forces_Weil_floor
end
end GaloisForLFunctions.SignedArithmeticCorrespondences
