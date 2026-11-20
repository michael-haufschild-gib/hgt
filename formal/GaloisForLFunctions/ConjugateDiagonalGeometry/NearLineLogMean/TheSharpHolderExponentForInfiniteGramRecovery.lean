import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromSuccessiveLogWindows

/-!
# The sharp Hölder exponent for recovery of an infinite Gram matrix

Successive log-window energies resolve the coefficient pair (i,j) at
bandwidth 1/(1+min(i,j)). Combining this loss with the tail of the
coefficients is the scale tradeoff in Bianchi–He (arXiv:2611.23490,
Lemma 2.2). Three adjacent coefficients attain the resulting exponent.
-/

noncomputable section
open Finset Complex RHTower RHTower.Sieve Filter Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- The logarithm of any other positive integer is at least (m+1)⁻¹ from log m. -/
theorem local_log_spacing {m j : ℕ} (hm : 0 < m) (hj : 0 < j) (hne : j ≠ m) :
    ((m:ℝ)+1)⁻¹ ≤ |Real.log j-Real.log m| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le hj hm hne hlt.le le_rfl
    exact (inv_anti₀ (Nat.cast_pos.mpr hm) (by linarith : (m:ℝ) ≤ m+1)).trans hh
  · have hs := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le (Nat.succ_pos m) hm
      (Nat.succ_ne_self m) le_rfl (Nat.le_succ m)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr (Nat.le_succ m))
    rw [abs_of_nonneg (sub_nonneg.mpr hlog),Nat.cast_succ] at hs
    have ht := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos m)) (Nat.cast_le.mpr hgt)
    exact hs.trans ((sub_le_sub_right (by simpa only [Nat.cast_succ] using ht) _).trans (le_abs_self _))

/-- Cofactor-local bandwidth: observation at even a very late prefix costs
only the smaller of the two indices. -/
theorem read_gram_local (a : ℕ → ℂ) {N m : ℕ} (hm : m ∈ Icc 1 N) {h : ℝ}
    (hh : 0 < h) (hcut : h ≤ ((m:ℝ)+1)⁻¹) :
    second (row a N) (gap N m) h/(2*h)=gram (a (N+1)) (a m) := by
  obtain ⟨hpos,hup⟩ := mem_Icc.mp hm
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr (hup.trans (Nat.le_succ _)))
  have hz := hcut.trans (local_log_spacing hpos (Nat.succ_pos N) (by omega : N+1 ≠ m))
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)] at hz
  change h ≤ gap N m at hz
  have hsep (j : ℕ) (hj : j ∈ Icc 1 N) (hne : j ≠ m) : h ≤ |gap N m-gap N j| := by
    rw [show gap N m-gap N j=Real.log j-Real.log m by dsimp [gap]; ring]
    exact hcut.trans (local_log_spacing hpos (mem_Icc.mp hj).1 hne)
  exact read_gram_of_separation a hm hh hz hsep

private theorem gram_size (z w : ℂ) : |gram z w| ≤ ‖z‖*‖w‖ :=
  (Complex.abs_re_le_norm (z*conj w)).trans_eq (by rw [norm_mul,Complex.norm_conj])

/-- Uniform noise in the original energy data is amplified at most linearly
in the smaller index, including on the diagonal. -/
theorem gram_error_smaller_index {a b : ℕ → ℂ} {δ : ℝ}
    (he : ∀ N d, |energy a N d-energy b N d| ≤ δ) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    |gram (a n) (a m)-gram (b n) (b m)| ≤ 4*δ*((m:ℝ)+1) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (he 0 0)
  obtain ⟨N,rfl⟩ : ∃ N, n=N+1 := ⟨n-1,by omega⟩
  let h := ((m:ℝ)+1)⁻¹
  have hp : 0 < h := by dsimp [h]; positivity
  have hr (d : ℝ) : |row a N d-row b N d| ≤ 2*δ := by
    unfold row
    rw [show ∀ x y z w : ℝ, x-y-(z-w)=(x-z)-(y-w) by intros; ring]
    exact (abs_sub _ _).trans (by linarith only [he (N+1) d,he N d])
  rcases Nat.eq_or_lt_of_le hmn with hd | hl
  · subst m
    have hwidth : h ≤ ((N+1:ℕ):ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have hd := hr h
    rw [row_diagonal a N hp.le hwidth,row_diagonal b N hp.le hwidth,←sub_mul,abs_mul,abs_of_pos hp] at hd
    simp only [gram_self]
    have hd' := (le_div_iff₀ hp).mpr hd
    dsimp only [h] at hd'
    rw [div_inv_eq_mul] at hd'
    exact hd'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · let g := gap N m
    have hread (v : ℕ → ℂ) := read_gram_local v (mem_Icc.mpr ⟨hm,Nat.lt_succ_iff.mp hl⟩) hp (le_refl h)
    rw [← hread a,← hread b,←sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*h)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hcancel : 4*δ*((m:ℝ)+1)*(2*h)=8*δ := by
      dsimp only [h]; field_simp [show (m:ℝ)+1≠0 by positivity] <;> ring
    rw [hcancel,abs_le]
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hr (g-h))
    obtain ⟨h₃,h₄⟩ := abs_le.mp (hr g)
    obtain ⟨h₅,h₆⟩ := abs_le.mp (hr (g+h))
    change -(8*δ) ≤ second (row a N) g h-second (row b N) g h ∧ _
    dsimp only [second]
    constructor <;> linarith only [h₁,h₂,h₃,h₄,h₅,h₆]

/-- A unit polynomial envelope on the positive-index coefficients. -/
def powerEnvelope (s : ℝ) (a : ℕ → ℂ) := ∀ n : ℕ, 0 < n → ‖a n‖ ≤ ((n:ℝ)+1)^(-s)

private theorem small_gram {a b : ℕ → ℂ} {s : ℝ} (hs : 0 < s) (ha : powerEnvelope s a)
    (hb : powerEnvelope s b) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    |gram (a n) (a m)-gram (b n) (b m)| ≤ 2*((m:ℝ)+1)^(-(2*s)) := by
  let X := (m:ℝ)+1
  have hX : 0 < X := by dsimp only [X]; positivity
  have htail := Real.rpow_le_rpow_of_nonpos hX (add_le_add (Nat.cast_le.mpr hmn) (le_refl (1:ℝ))) (neg_nonpos.mpr hs.le)
  have hg (v : ℕ → ℂ) (hv : powerEnvelope s v) : |gram (v n) (v m)| ≤ X^(-(2*s)) := by
    rw [show -(2*s)= -s+ -s by ring,Real.rpow_add hX]
    exact (gram_size _ _).trans (mul_le_mul ((hv n (hm.trans_le hmn)).trans htail)
      (hv m hm) (norm_nonneg _) (Real.rpow_nonneg hX.le _))
  exact (abs_sub _ _).trans (by linarith only [hg a ha,hg b hb])

/-- The entire infinite real Gram matrix has Hölder exponent 2s/(1+2s)
on sequences whose nth coefficient is at most (1+n)^(-s). -/
theorem power_envelope_gram_holder {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    {a b : ℕ → ℂ} (ha : powerEnvelope s a) (hb : powerEnvelope s b)
    (he : ∀ N d, |energy a N d-energy b N d| ≤ δ) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    |gram (a i) (a j)-gram (b i) (b j)| ≤ 4*δ^(2*s/(1+2*s)) := by
  have ordered (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
      |gram (a n) (a m)-gram (b n) (b m)| ≤ 4*δ^(2*s/(1+2*s)) := by
    let R := δ^(-(1/(1+2*s)))
    have hR : 0 < R := Real.rpow_pos_of_pos hδ _
    have hden : 1+2*s≠0 := by positivity
    rcases le_total ((m:ℝ)+1) R with h | h
    · refine (gram_error_smaller_index he hm hmn).trans ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_)
      dsimp only [R]
      -- Combine the first power of the noise with its balancing scale.
      calc
        _ = 4*(δ^((1:ℝ) + -(1/(1+2*s)))) := by rw [Real.rpow_add hδ,Real.rpow_one]; ring
        _ = _ := by congr 2; field_simp; ring
    · have hmono := Real.rpow_le_rpow_of_nonpos hR h (neg_nonpos.mpr (by positivity : 0 ≤ 2*s))
      have hpow : R^(-(2*s))=δ^(2*s/(1+2*s)) := by
        dsimp only [R]; rw [←Real.rpow_mul hδ.le]; congr 1; ring
      rw [hpow] at hmono
      exact (small_gram hs ha hb hm hmn).trans (by linarith only [hmono,Real.rpow_nonneg hδ.le (2*s/(1+2*s))])
  rcases le_total j i with h | h
  · exact ordered j i hj h
  · rw [gram_comm (a i),gram_comm (b i)]
    exact ordered i j hi h

/-- An adjacent pair of opposite coefficients, followed by a signed test coefficient. -/
def adjacentTriple (n : ℕ) (t u : ℝ) (k : ℕ) : ℂ :=
  if k=n then (t:ℂ) else if k=n+1 then -(t:ℂ) else if k=n+2 then (u:ℂ) else 0

private theorem triple_at_last (n : ℕ) (t u : ℝ) : adjacentTriple n t u (n+2)=(u:ℂ) := by
  simp [adjacentTriple]

private theorem triple_before (n : ℕ) (t u v : ℝ) {k : ℕ} (hk : k ≤ n+1) :
    adjacentTriple n t u k=adjacentTriple n t v k := by
  simp [adjacentTriple,show k≠n+2 by omega]

private theorem energy_before (n : ℕ) (t u v : ℝ) {k : ℕ} (hk : k ≤ n+1) (d : ℝ) :
    energy (adjacentTriple n t u) k d=energy (adjacentTriple n t v) k d := by
  simp only [energy,integral_normSq_logWindowSum]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [triple_before n t u v ((mem_Icc.mp hi).2.trans hk),triple_before n t u v ((mem_Icc.mp hj).2.trans hk)]

private theorem energy_after (n : ℕ) (t u : ℝ) (d : ℝ) {k : ℕ} (hk : n+2 ≤ k) :
    energy (adjacentTriple n t u) k d=energy (adjacentTriple n t u) (n+2) d := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction r with
  | zero => simp
  | succ r ih =>
    let k := n+2+r
    have hz : adjacentTriple n t u (k+1)=0 := by
      simp only [adjacentTriple,if_neg (show k+1≠n by dsimp [k]; omega),
        if_neg (show k+1≠n+1 by dsimp [k]; omega),if_neg (show k+1≠n+2 by dsimp [k]; omega)]
    have hr := row_spectrum (adjacentTriple n t u) k d
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul,gram,zero_re,zero_add,sum_const_zero,mul_zero] at hr
    exact (sub_eq_zero.mp hr).trans ih

private theorem triple_last_row {n : ℕ} (hn : 0 < n) (t u d : ℝ) :
    row (adjacentTriple n t u) (n+1) d =
      u^2*max d 0+2*(u*t)*(max (d-gap (n+1) n) 0-max (d-gap (n+1) (n+1)) 0) := by
  let v := adjacentTriple n t u
  have hpair (a b : ℝ) : gram (a:ℂ) (b:ℂ)=a*b := by simp [gram,←Complex.ofReal_mul]
  have hterm (j : ℕ) (hj : j∈Icc 1 (n+1)) :
      gram (v (n+2)) (v j)*max (d-gap (n+1) j) 0 =
        (if j=n then u*t*max (d-gap (n+1) n) 0 else 0) +
        (if j=n+1 then -(u*t)*max (d-gap (n+1) (n+1)) 0 else 0) := by
    change gram (adjacentTriple n t u (n+2)) _*_ = _
    rw [triple_at_last]
    by_cases h₁ : j=n
    · subst j; simp [v,adjacentTriple,hpair]
    by_cases h₂ : j=n+1
    · subst j
      simp only [v,adjacentTriple,if_neg h₁,ite_true,zero_add]
      rw [←Complex.ofReal_neg,hpair,mul_neg]
    have h₃ : j≠n+2 := by have := (mem_Icc.mp hj).2; omega
    simp [v,adjacentTriple,h₁,h₂,h₃,gram]
  rw [row_spectrum,sum_congr rfl hterm,sum_add_distrib,sum_ite_eq',sum_ite_eq',
    if_pos (mem_Icc.mpr ⟨hn,Nat.le_succ n⟩),if_pos (mem_Icc.mpr ⟨Nat.succ_pos n,le_rfl⟩),
    triple_at_last,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

/-- Two Gram matrices separated by 2t² have all their energy curves within
4t² log(1+1/n) of each other, including at arbitrarily large bandwidth. -/
theorem adjacent_triple_energy_gap {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (∀ k d, |energy (adjacentTriple n t t) k d-energy (adjacentTriple n t (-t)) k d| ≤ 
      4*t^2*((n:ℝ)⁻¹)) ∧
    |gram (adjacentTriple n t t (n+2)) (adjacentTriple n t t n)-
      gram (adjacentTriple n t (-t) (n+2)) (adjacentTriple n t (-t) n)|=2*t^2 := by
  constructor
  · intro k d
    rcases le_or_gt k (n+1) with hk | hk
    · rw [energy_before n t t (-t) hk,sub_self,abs_zero]; positivity
    rw [energy_after n t t d hk,energy_after n t (-t) d hk]
    have ha := triple_last_row hn t t d
    have hb := triple_last_row hn t (-t) d
    have hzero := energy_before n t t (-t) (le_refl (n+1)) d
    let g := gap (n+1) n
    let v := gap (n+1) (n+1)
    have hform : energy (adjacentTriple n t t) (n+2) d-energy (adjacentTriple n t (-t)) (n+2) d =
        4*t^2*(max (d-g) 0-max (d-v) 0) := by
      unfold row at ha hb
      dsimp only [g,v]
      linear_combination ha-hb+hzero
    have ht := abs_max_sub_max_le_abs (d-g) (d-v) 0
    have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hl := Real.log_le_log hn₀ (Nat.cast_le.mpr (Nat.le_succ n))
    have hlog : |(d-g)-(d-v)| ≤ (n:ℝ)⁻¹ := by
      rw [show (d-g)-(d-v)= -(Real.log (n+1:ℕ)-Real.log n) by dsimp [g,v,gap]; ring,
        abs_neg,abs_of_nonneg (sub_nonneg.mpr hl),
        ← Real.log_div (by positivity) hn₀.ne',Nat.cast_succ]
      have hg := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (n:ℝ)+1) hn₀)
      exact hg.trans_eq (by field_simp [hn₀.ne']; ring)
    rw [hform,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*t^2)]
    exact mul_le_mul_of_nonneg_left (ht.trans hlog) (by positivity)
  · rw [triple_at_last,triple_at_last]
    have hfirst (w : ℝ) : adjacentTriple n t w n = (t : ℂ) := by simp [adjacentTriple]
    rw [hfirst t, hfirst (-t)]
    simp only [gram,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re]
    rw [show t*t- -t*t=2*t^2 by ring,abs_of_nonneg (by positivity)]

private theorem triple_power_envelope {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 3 ≤ n) :
    let t := (2*(n:ℝ))^(-s)
    powerEnvelope s (adjacentTriple n t t) ∧ powerEnvelope s (adjacentTriple n t (-t)) := by
  intro t
  have hn₀ : (3:ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have h (u : ℝ) (hu : |u|=t) : powerEnvelope s (adjacentTriple n t u) := by
    intro k _
    by_cases hk : k ≤ n+2
    · have hkn : (k:ℝ)+1 ≤ 2*(n:ℝ) := by exact_mod_cast (show k+1 ≤ 2*n by omega)
      have ht' := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (k:ℝ)+1) hkn (neg_nonpos.mpr hs.le)
      suffices hnrm : ‖adjacentTriple n t u k‖ ≤ t by exact hnrm.trans ht'
      unfold adjacentTriple
      split_ifs <;> simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,hu,ht]
    · simp [adjacentTriple,show k≠n by omega,show k≠n+1 by omega,show k≠n+2 by omega,
        Real.rpow_nonneg (by positivity : 0 ≤ (k:ℝ)+1)]
  exact ⟨h t (abs_of_nonneg ht),h (-t) (by rw [abs_neg,abs_of_nonneg ht])⟩

/-- No larger power of the uniform energy error bounds the Gram error
on the same unit envelope, even when both sequences have only three entries. -/
theorem power_envelope_holder_optimal {s γ : ℝ} (hs : 0 < s) (hγ : 2*s/(1+2*s) < γ) (K : ℝ) :
    ∃ (a b : ℕ → ℂ) (δ : ℝ), powerEnvelope s a ∧ powerEnvelope s b ∧ 0 < δ ∧
      (∀ N d, |energy a N d-energy b N d| ≤ δ) ∧
      ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ K*δ^γ < |gram (a i) (a j)-gram (b i) (b j)| := by
  let A := (2:ℝ)^(-2*s)
  let e := γ*(1+2*s)-2*s
  have hden : 0 < 1+2*s := by positivity
  have he : 0 < e := sub_pos.mpr ((div_lt_iff₀ hden).mp hγ)
  have ha : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hlim := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn,hbig⟩ := ((eventually_ge_atTop 3).and
    (hlim.eventually_gt_atTop (K*(4*A)^γ/(2*A)))).exists
  have hn₀ : 0 < n := by omega
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn₀
  let t := (2*(n:ℝ))^(-s)
  let δ := 4*t^2*(n:ℝ)⁻¹
  obtain ⟨henv,henv'⟩ := triple_power_envelope hs hn
  obtain ⟨hgap,hdist⟩ := adjacent_triple_energy_gap hn₀ t
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨_,_,δ,henv,henv',by dsimp [δ]; positivity,hgap,n+2,n,by omega,hn₀,?_⟩
  rw [hdist]
  have hts : t^2=A*(n:ℝ)^(-2*s) := by
    rw [← Real.rpow_natCast t 2,← Real.rpow_mul (by positivity : 0 ≤ 2*(n:ℝ)),
      Real.mul_rpow (by norm_num) hn'.le]
    dsimp only [A]
    norm_num
    <;> ring_nf
  have hds : δ = (4*A)*(n:ℝ)^(-(1+2*s)) := by
    dsimp only [δ]
    rw [hts,show -(1+2*s)= -2*s+(-1) by ring,Real.rpow_add hn',Real.rpow_neg_one]
    ring
  change K*(4*A)^γ/(2*A) < (n:ℝ)^e at hbig
  have hx := (div_lt_iff₀ (by positivity : 0 < 2*A)).mp hbig
  have hy := mul_lt_mul_of_pos_right hx (Real.rpow_pos_of_pos hn' (-(1+2*s)*γ))
  rw [hds,Real.mul_rpow (by positivity) (Real.rpow_nonneg hn'.le _),←Real.rpow_mul hn'.le,hts]
  calc
    _ = K*(4*A)^γ*(n:ℝ)^(-(1+2*s)*γ) := by ring
    _ < (n:ℝ)^e*(2*A)*(n:ℝ)^(-(1+2*s)*γ) := hy
    _ = (2*A)*((n:ℝ)^e*(n:ℝ)^(-(1+2*s)*γ)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hn',show e+ -(1+2*s)*γ= -2*s by dsimp [e]; ring]
      ring

#print axioms read_gram_local
#print axioms power_envelope_gram_holder
#print axioms adjacent_triple_energy_gap
#print axioms power_envelope_holder_optimal
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
