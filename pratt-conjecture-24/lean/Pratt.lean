import Std

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

namespace Pratt

abbrev Digit := Fin 7
abbrev Edge := Digit × Digit × Digit

def edges : List Edge := [(0,0,6),(0,5,1),(0,6,0),(1,0,5),(2,3,1),(2,4,0),(4,1,1),(4,2,0)]
def X (a b c : Digit) : Prop := (a,b,c) ∈ edges
instance (a b c : Digit) : Decidable (X a b c) := inferInstanceAs (Decidable ((a,b,c) ∈ edges))
def A (a : Digit) : Prop := a ∈ ([0,1,2,4] : List Digit)
def B (_ : Digit) : Prop := True
def C (c : Digit) : Prop := c ∈ ([0,1,5,6] : List Digit)
instance (a : Digit) : Decidable (A a) := inferInstanceAs (Decidable (a ∈ ([0,1,2,4] : List Digit)))
instance (c : Digit) : Decidable (C c) := inferInstanceAs (Decidable (c ∈ ([0,1,5,6] : List Digit)))
def u (a : Digit) : Int := if a = 1 then 1 else 0
def v (b : Digit) : Int := if b = 0 then -2 else 0
def w (c : Digit) : Int := if c = 5 then 1 else if c = 6 then 2 else 0

def ETF {α : Type} (R : α → α → α → Prop) : Prop :=
  (∀ a' b' a b c d e f, R a' b c → R a b' c → R a' e f → R d b' f → (a,b,c) = (d,e,f)) ∧
  (∀ a' c' a b c d e f, R a' b c → R a b c' → R a' e f → R d e c' → (a,b,c) = (d,e,f)) ∧
  (∀ b' c' a b c d e f, R a b' c → R a b c' → R d b' f → R d e c' → (a,b,c) = (d,e,f))

-- Check the finite relation by enumerating the four edges, not all eight variables.
theorem digitETF : ETF X := by
  constructor
  · intro a' b' a b c d e f h1 h2 h3 h4
    simp [X, edges] at h1 h2 h3 h4
    rcases h1 with h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl⟩ <;> simp_all <;> grind (splits := 30)
  constructor
  · intro a' c' a b c d e f h1 h2 h3 h4
    simp [X, edges] at h1 h2 h3 h4
    rcases h1 with h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl⟩ <;> simp_all <;> grind (splits := 30)
  · intro b' c' a b c d e f h1 h2 h3 h4
    simp [X, edges] at h1 h2 h3 h4
    rcases h1 with h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl⟩ <;> simp_all <;> grind (splits := 30)

set_option maxHeartbeats 4000000 in
theorem digitFilter : ∀ a b c : Digit, A a → C c → a.val + b.val + c.val = 6 →
    0 ≤ u a + v b + w c ∧ (u a + v b + w c = 0 ↔ X a b c) := by decide

set_option maxHeartbeats 4000000 in
theorem digitEdge : ∀ a b c : Digit, X a b c → A a ∧ C c ∧ a.val+b.val+c.val=6 ∧ u a+v b+w c=0 := by decide

def enc : List Digit → Nat
  | [] => 0
  | d :: ds => d.val + 7 * enc ds

def mass : List Digit → Nat
  | [] => 0
  | d :: ds => d.val + mass ds

def weight (f : Digit → Int) : List Digit → Int
  | [] => 0
  | d :: ds => f d + weight f ds

def WordEdge : List Digit → List Digit → List Digit → Prop
  | [], [], [] => True
  | a::as, b::bs, c::cs => X a b c ∧ WordEdge as bs cs
  | _,_,_ => False

def cap (n : Nat) := 7^n-1

theorem cap_succ (n : Nat) : cap (n+1) = 6 + 7 * cap n := by
  have h : 0 < 7^n := Nat.pow_pos (by decide)
  simp [cap, Nat.pow_succ]
  omega

theorem enc_bound (a : List Digit) : enc a ≤ cap a.length := by
  induction a with
  | nil => decide
  | cons d ds ih =>
    simp only [enc, List.length_cons, cap_succ]
    have := d.isLt
    omega

theorem enc_injective {a b : List Digit} (hl : a.length = b.length) (h : enc a = enc b) : a = b := by
  induction a generalizing b with
  | nil => simpa using hl.symm
  | cons d ds ih =>
    cases b with
    | nil => simp at hl
    | cons e es =>
      simp only [enc] at h
      have hd := d.isLt
      have he := e.isLt
      have hde : d = e := Fin.ext (by omega)
      have ht : enc ds = enc es := by omega
      have hlen : ds.length = es.length := by simpa using hl
      rw [hde, ih hlen ht]

-- The nonnegative carry has a mass cost of six per internal boundary.
theorem mass_lower (a b c : List Digit) (q : Nat)
    (hb : b.length = a.length) (hc : c.length = a.length)
    (h : enc a + enc b + enc c + q = cap a.length) :
    6 * a.length ≤ mass a + mass b + mass c + q := by
  induction a generalizing b c q with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero]
    omega
  | cons x xs ih =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      cases c with
      | nil => simp at hc
      | cons z zs =>
        simp only [enc, List.length_cons, cap_succ] at h
        have hd : (x.val + y.val + z.val + q) % 7 = 6 := by omega
        let t := (x.val + y.val + z.val + q) / 7
        have ht : x.val + y.val + z.val + q = 6 + 7*t := by omega
        have htail : enc xs + enc ys + enc zs + t = cap xs.length := by omega
        have hi := ih ys zs t (by simpa using hb) (by simpa using hc) htail
        simp only [mass, List.length_cons]
        omega

theorem word_filter_aux (a b c : List Digit)
    (hb : b.length = a.length) (hc : c.length = a.length)
    (haA : ∀ x ∈ a, A x) (hcC : ∀ x ∈ c, C x)
    (hs : enc a + enc b + enc c = cap a.length)
    (hm : mass a + mass b + mass c = 6 * a.length) :
    0 ≤ weight u a + weight v b + weight w c ∧
      (weight u a + weight v b + weight w c = 0 → WordEdge a b c) := by
  induction a generalizing b c with
  | nil =>
    have hb' : b = [] := by simpa using hb
    have hc' : c = [] := by simpa using hc
    simp [hb',hc',WordEdge,weight]
  | cons x xs ih =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      cases c with
      | nil => simp at hc
      | cons z zs =>
        simp only [enc, List.length_cons, cap_succ] at hs
        simp only [mass, List.length_cons] at hm
        have hd : (x.val + y.val + z.val) % 7 = 6 := by omega
        let t := (x.val + y.val + z.val) / 7
        have ht : x.val + y.val + z.val = 6 + 7*t := by omega
        have htail : enc xs + enc ys + enc zs + t = cap xs.length := by omega
        have hbl : ys.length = xs.length := by simpa using hb
        have hcl : zs.length = xs.length := by simpa using hc
        have hi := mass_lower xs ys zs t hbl hcl htail
        have hz : t = 0 := by omega
        have hsum : x.val + y.val + z.val = 6 := by omega
        have hf := digitFilter x y z (haA x (by simp)) (hcC z (by simp)) hsum
        -- We still need nonnegativity of the remaining weights.
        have htail' : enc xs + enc ys + enc zs = cap xs.length := by omega
        have hm' : mass xs + mass ys + mass zs = 6 * xs.length := by omega
        have hrec := ih ys zs hbl hcl
          (fun d hd => haA d (by simp [hd])) (fun d hd => hcC d (by simp [hd])) htail' hm'
        simp only [weight]
        refine ⟨by omega, ?_⟩
        intro hw
        have h0 : u x + v y + w z = 0 := by omega
        have h1 : weight u xs + weight v ys + weight w zs = 0 := by omega
        exact ⟨hf.2.mp h0, hrec.2 h1⟩

theorem word_filter (a b c : List Digit)
    (hb : b.length = a.length) (hc : c.length = a.length)
    (haA : ∀ x ∈ a, A x) (hcC : ∀ x ∈ c, C x)
    (hs : enc a + enc b + enc c = cap a.length)
    (hm : mass a + mass b + mass c = 6 * a.length)
    (hw : weight u a + weight v b + weight w c = 0) : WordEdge a b c :=
  (word_filter_aux a b c hb hc haA hcC hs hm).2 hw


theorem word_lengths {a b c : List Digit} (h : WordEdge a b c) : a.length = b.length ∧ a.length = c.length := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp_all [WordEdge] <;> exact ih h.2
  | cons x xs ih =>
    cases b <;> cases c <;> simp_all [WordEdge] <;> exact ih h.2

theorem word_get {a b c : List Digit} (h : WordEdge a b c) (i : Nat)
    (ha : i < a.length) (hb : i < b.length) (hc : i < c.length) : X a[i] b[i] c[i] := by
  induction a generalizing b c i with
  | nil => simp at ha
  | cons x xs ih =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      cases c with
      | nil => simp at hc
      | cons z zs =>
        cases i with
        | zero => exact h.1
        | succ i => exact ih h.2 i (by simpa using ha) (by simpa using hb) (by simpa using hc)

theorem wordETF : ETF WordEdge := by
  constructor
  · intro a' b' a b c d e f h1 h2 h3 h4
    obtain ⟨hl1, hr1⟩ := word_lengths h1
    obtain ⟨hl2, hr2⟩ := word_lengths h2
    obtain ⟨hl3, hr3⟩ := word_lengths h3
    obtain ⟨hl4, hr4⟩ := word_lengths h4
    have heq : ∀ i (hi : i < a.length), (a[i],b[i]' (by omega),c[i]' (by omega)) = (d[i]' (by omega),e[i]' (by omega),f[i]' (by omega)) := by
      intro i hi
      exact digitETF.1 ((a')[i]'(by omega)) ((b')[i]'(by omega)) _ _ _ _ _ _
        (word_get h1 i (by omega) (by omega) (by omega))
        (word_get h2 i (by omega) (by omega) (by omega))
        (word_get h3 i (by omega) (by omega) (by omega))
        (word_get h4 i (by omega) (by omega) (by omega))
    have ha : a = d := List.ext_getElem (by omega) (fun i hi _ => congrArg Prod.fst (heq i hi))
    have hb : b = e := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.1) (heq i (by omega)))
    have hc : c = f := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.2) (heq i (by omega)))
    rw [ha,hb,hc]
  constructor
  · intro a' c' a b c d e f h1 h2 h3 h4
    obtain ⟨hl1, hr1⟩ := word_lengths h1
    obtain ⟨hl2, hr2⟩ := word_lengths h2
    obtain ⟨hl3, hr3⟩ := word_lengths h3
    obtain ⟨hl4, hr4⟩ := word_lengths h4
    have heq : ∀ i (hi : i < a.length), (a[i],b[i]' (by omega),c[i]' (by omega)) = (d[i]' (by omega),e[i]' (by omega),f[i]' (by omega)) := by
      intro i hi
      exact digitETF.2.1 ((a')[i]'(by omega)) ((c')[i]'(by omega)) _ _ _ _ _ _
        (word_get h1 i (by omega) (by omega) (by omega))
        (word_get h2 i (by omega) (by omega) (by omega))
        (word_get h3 i (by omega) (by omega) (by omega))
        (word_get h4 i (by omega) (by omega) (by omega))
    have ha : a = d := List.ext_getElem (by omega) (fun i hi _ => congrArg Prod.fst (heq i hi))
    have hb : b = e := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.1) (heq i (by omega)))
    have hc : c = f := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.2) (heq i (by omega)))
    rw [ha,hb,hc]
  · intro b' c' a b c d e f h1 h2 h3 h4
    obtain ⟨hl1, hr1⟩ := word_lengths h1
    obtain ⟨hl2, hr2⟩ := word_lengths h2
    obtain ⟨hl3, hr3⟩ := word_lengths h3
    obtain ⟨hl4, hr4⟩ := word_lengths h4
    have heq : ∀ i (hi : i < a.length), (a[i],b[i]' (by omega),c[i]' (by omega)) = (d[i]' (by omega),e[i]' (by omega),f[i]' (by omega)) := by
      intro i hi
      exact digitETF.2.2 ((b')[i]'(by omega)) ((c')[i]'(by omega)) _ _ _ _ _ _
        (word_get h1 i (by omega) (by omega) (by omega))
        (word_get h2 i (by omega) (by omega) (by omega))
        (word_get h3 i (by omega) (by omega) (by omega))
        (word_get h4 i (by omega) (by omega) (by omega))
    have ha : a = d := List.ext_getElem (by omega) (fun i hi _ => congrArg Prod.fst (heq i hi))
    have hb : b = e := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.1) (heq i (by omega)))
    have hc : c = f := List.ext_getElem (by omega) (fun i hi _ => congrArg (fun p => p.2.2) (heq i (by omega)))
    rw [ha,hb,hc]


-- Coarse marginal types suffice; the full histograms of v68 are unnecessary.
structure Marginal where
  ma : Nat
  mb : Nat
  mc : Nat
  wa : Int
  wb : Int
  wc : Int
  deriving DecidableEq

def Good (n : Nat) (s : Marginal) : Prop :=
  s.ma + s.mb + s.mc = 6*n ∧ s.wa + s.wb + s.wc = 0

def roleA (n : Nat) (s : Marginal) (l : List Digit) : Prop :=
  l.length = n ∧ (∀ x ∈ l, A x) ∧ mass l = s.ma ∧ weight u l = s.wa

def roleB (n : Nat) (s : Marginal) (l : List Digit) : Prop :=
  l.length = n ∧ mass l = s.mb ∧ weight v l = s.wb

def roleC (n : Nat) (s : Marginal) (l : List Digit) : Prop :=
  l.length = n ∧ (∀ x ∈ l, C x) ∧ mass l = s.mc ∧ weight w l = s.wc

def modulus (n : Nat) := 3 * cap n + 1

def shift (h c : Nat) := (c + (2*h+1)) % (3*h+1)

def unshift (h c : Nat) := (c+h) % (3*h+1)

theorem shift_bound (h c : Nat) : shift h c < 3*h+1 := Nat.mod_lt _ (by omega)

theorem unshift_shift {h c : Nat} (hc : c ≤ h) : unshift h (shift h c) = c := by
  unfold unshift shift
  rw [Nat.mod_add_mod]
  have he : c + (2*h+1) + h = c + (3*h+1)*1 := by omega
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem shifted_sum {h a b c : Nat} (ha : a ≤ h) (hb : b ≤ h) (hc : c ≤ h) :
    (a+b+shift h c) % (3*h+1) = 0 ↔ a+b+c=h := by
  unfold shift
  rw [Nat.add_mod_mod]
  have he : a+b+(c+(2*h+1)) = a+b+c+2*h+1 := by omega
  rw [he]
  by_cases hh : a+b+c+2*h+1 < 3*h+1
  · rw [Nat.mod_eq_of_lt hh]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

def decode (n a : Nat) : List Digit :=
  match n with
  | 0 => []
  | n+1 => ⟨a%7, Nat.mod_lt _ (by decide)⟩ :: decode n (a/7)

theorem decode_enc (l : List Digit) : decode l.length (enc l) = l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.length_cons, enc, decode]
    have hd := d.isLt
    have hmod : (d.val+7*enc ds)%7 = d.val := by omega
    have hdiv : (d.val+7*enc ds)/7 = enc ds := by omega
    simp only [hdiv,ih]
    exact congrArg (fun z : Digit => z :: ds) (Fin.ext hmod)

def setA (n : Nat) (s : Marginal) (a : Nat) := ∃ l, roleA n s l ∧ enc l = a

def setB (n : Nat) (s : Marginal) (b : Nat) := ∃ l, roleB n s l ∧ enc l = b

def setC (n : Nat) (s : Marginal) (c : Nat) := ∃ l, roleC n s l ∧ shift (cap n) (enc l) = c

def CyclicEdge (N : Nat) (P Q R : Nat → Prop) (a b c : Nat) : Prop :=
  a < N ∧ b < N ∧ c < N ∧ P a ∧ Q b ∧ R c ∧ (a+b+c)%N = 0

def target (n : Nat) (s : Marginal) := CyclicEdge (modulus n) (setA n s) (setB n s) (setC n s)

def recoverA (n a : Nat) := decode n a

def recoverB (n b : Nat) := decode n b

def recoverC (n c : Nat) := decode n (unshift (cap n) c)

theorem target_decode {n : Nat} {s : Marginal} (hg : Good n s) {a b c : Nat} (h : target n s a b c) :
    WordEdge (recoverA n a) (recoverB n b) (recoverC n c) ∧
    enc (recoverA n a) = a ∧ enc (recoverB n b) = b ∧ shift (cap n) (enc (recoverC n c)) = c := by
  obtain ⟨_,_,_,⟨al,ha,hae⟩,⟨bl,hb,hbe⟩,⟨cl,hc,hce⟩,hs⟩ := h
  obtain ⟨hla,hAa,hma,hwa⟩ := ha
  obtain ⟨hlb,hmb,hwb⟩ := hb
  obtain ⟨hlc,hCc,hmc,hwc⟩ := hc
  subst a
  subst b
  subst c
  have ba : enc al ≤ cap n := by simpa [hla] using enc_bound al
  have bb : enc bl ≤ cap n := by simpa [hlb] using enc_bound bl
  have bc : enc cl ≤ cap n := by simpa [hlc] using enc_bound cl
  have hsum : enc al + enc bl + enc cl = cap n := (shifted_sum ba bb bc).mp hs
  have hda : recoverA n (enc al) = al := by unfold recoverA; rw [← hla, decode_enc]
  have hdb : recoverB n (enc bl) = bl := by unfold recoverB; rw [← hlb, decode_enc]
  have hdc : recoverC n (shift (cap n) (enc cl)) = cl := by unfold recoverC; rw [unshift_shift bc, ← hlc, decode_enc]
  rw [hda,hdb,hdc]
  refine ⟨word_filter al bl cl (by omega) (by omega) hAa hCc (by simpa [hla] using hsum) ?_ ?_, rfl,rfl,rfl⟩
  · rw [hma,hmb,hmc,hla]; exact hg.1
  · rw [hwa,hwb,hwc]; exact hg.2

theorem targetETF {n : Nat} {s : Marginal} (hg : Good n s) : ETF (target n s) := by
  constructor
  · intro a' b' a b c d e f h1 h2 h3 h4
    obtain ⟨e1, a1, b1, c1⟩ := target_decode hg h1
    obtain ⟨e2, a2, b2, c2⟩ := target_decode hg h2
    obtain ⟨e3, a3, b3, c3⟩ := target_decode hg h3
    obtain ⟨e4, a4, b4, c4⟩ := target_decode hg h4
    have he := wordETF.1 (recoverA n a') (recoverB n b') _ _ _ _ _ _ e1 e2 e3 e4
    have ha := congrArg Prod.fst he
    have hb := congrArg (fun p => p.2.1) he
    have hc := congrArg (fun p => p.2.2) he
    simp only at ha hb hc
    grind
  constructor
  · intro a' c' a b c d e f h1 h2 h3 h4
    obtain ⟨e1, a1, b1, c1⟩ := target_decode hg h1
    obtain ⟨e2, a2, b2, c2⟩ := target_decode hg h2
    obtain ⟨e3, a3, b3, c3⟩ := target_decode hg h3
    obtain ⟨e4, a4, b4, c4⟩ := target_decode hg h4
    have he := wordETF.2.1 (recoverA n a') (recoverC n c') _ _ _ _ _ _ e1 e2 e3 e4
    have ha := congrArg Prod.fst he
    have hb := congrArg (fun p => p.2.1) he
    have hc := congrArg (fun p => p.2.2) he
    simp only at ha hb hc
    grind
  · intro b' c' a b c d e f h1 h2 h3 h4
    obtain ⟨e1, a1, b1, c1⟩ := target_decode hg h1
    obtain ⟨e2, a2, b2, c2⟩ := target_decode hg h2
    obtain ⟨e3, a3, b3, c3⟩ := target_decode hg h3
    obtain ⟨e4, a4, b4, c4⟩ := target_decode hg h4
    have he := wordETF.2.2 (recoverB n b') (recoverC n c') _ _ _ _ _ _ e1 e2 e3 e4
    have ha := congrArg Prod.fst he
    have hb := congrArg (fun p => p.2.1) he
    have hc := congrArg (fun p => p.2.2) he
    simp only at ha hb hc
    grind


-- A finite pigeonhole lemma, proved over lists without any cardinality library.
theorem filter_partition {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !(p x))).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h] <;> omega

theorem one_bucket {α : Type} (key : α → Nat) (M : Nat) (l : List α)
    (hbound : ∀ x ∈ l, key x < M) :
    ∃ b : List α, b.Sublist l ∧ (∀ x ∈ b, ∀ y ∈ b, key x = key y) ∧
      l.length ≤ M*b.length := by
  induction M generalizing l with
  | zero =>
    cases l with
    | nil => exact ⟨[], List.nil_sublist _, by simp, by simp⟩
    | cons x xs => have := hbound x (by simp); omega
  | succ M ih =>
    let l₁ := l.filter (fun x => decide (key x = M))
    let l₀ := l.filter (fun x => !(decide (key x = M)))
    have hp : l₁.length + l₀.length = l.length := filter_partition _ _
    have h₀ : ∀ x ∈ l₀, key x < M := by
      intro x hx
      have hx' := List.mem_filter.mp hx
      have hb := hbound x hx'.1
      have hn : key x ≠ M := by simpa using hx'.2
      omega
    obtain ⟨b,hb,hkey,hcnt⟩ := ih l₀ h₀
    have hl₁ : ∀ x ∈ l₁, key x = M := by
      intro x hx; exact of_decide_eq_true (List.mem_filter.mp hx).2
    by_cases h : l₁.length ≤ b.length
    · refine ⟨b,hb.trans List.filter_sublist,hkey,?_⟩
      rw [Nat.succ_mul]
      omega
    · refine ⟨l₁,List.filter_sublist,fun x hx y hy => (hl₁ x hx).trans (hl₁ y hy).symm,?_⟩
      have h' : M*b.length ≤ M*l₁.length := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.succ_mul]
      omega

theorem many_buckets {α : Type} (keys : List (α → Nat)) (M : Nat) (l : List α)
    (hbound : ∀ f ∈ keys, ∀ x ∈ l, f x < M) :
    ∃ b : List α, b.Sublist l ∧ (∀ f ∈ keys, ∀ x ∈ b, ∀ y ∈ b, f x = f y) ∧
      l.length ≤ M^keys.length * b.length := by
  induction keys generalizing l with
  | nil => exact ⟨l,List.Sublist.refl _, by simp, by simp⟩
  | cons f fs ih =>
    obtain ⟨b,hb,hkey,hcnt⟩ := one_bucket f M l (hbound f (by simp))
    obtain ⟨c,hc,hkeys,hcnt'⟩ := ih b (fun g hg x hx => hbound g (by simp [hg]) x (hb.subset hx))
    refine ⟨c,hc.trans hb,?_,?_⟩
    · intro g hg x hx y hy
      rcases List.mem_cons.mp hg with rfl|hg
      · exact hkey x (hc.subset hx) y (hc.subset hy)
      · exact hkeys g hg x hx y hy
    · calc
        l.length ≤ M*b.length := hcnt
        _ ≤ M*(M^fs.length*c.length) := Nat.mul_le_mul_left _ hcnt'
        _ = M^(f::fs).length*c.length := by simp [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm]

-- The list of all length-n words on the eight allowed edges.
def allWords : Nat → List (List Edge)
  | 0 => [[]]
  | n+1 => edges.flatMap (fun e => (allWords n).map (fun l => e::l))

theorem words_length (n : Nat) : (allWords n).length = 8^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [allWords,edges,ih,Nat.pow_succ]
    omega

theorem prefixed_nodup {α : Type} (heads : List α) (tails : List (List α))
    (hh : heads.Nodup) (ht : tails.Nodup) :
    (heads.flatMap (fun x => tails.map (fun t => x::t))).Nodup := by
  induction heads with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,hn⟩ := List.nodup_cons.mp hh
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨?_,ih hn,?_⟩
    · apply List.pairwise_map.mpr
      exact ht.imp (fun h he => h (List.cons.inj he).2)
    · intro a ha b hb he
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,hym⟩ := List.mem_flatMap.mp hb
      obtain ⟨t',_,rfl⟩ := List.mem_map.mp hym
      exact hnot ((List.cons.inj he).1 ▸ hy)

theorem words_nodup (n : Nat) : (allWords n).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih => exact prefixed_nodup edges (allWords n) (by decide) ih

theorem words_props {n : Nat} {l : List Edge} (h : l ∈ allWords n) :
    l.length = n ∧ ∀ e ∈ l, e ∈ edges := by
  induction n generalizing l with
  | zero => simp [allWords] at h; subst l; simp
  | succ n ih =>
    obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp h
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
    obtain ⟨hl,hh⟩ := ih ht
    refine ⟨by simp [hl],?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact hh f hf

def wordA (l : List Edge) := l.map Prod.fst
def wordB (l : List Edge) := l.map (fun e => e.2.1)
def wordC (l : List Edge) := l.map (fun e => e.2.2)

def marginal (l : List Edge) : Marginal :=
  ⟨mass (wordA l), mass (wordB l), mass (wordC l),
    weight u (wordA l),weight v (wordB l),weight w (wordC l)⟩

theorem wordA_len (l : List Edge) : (wordA l).length = l.length := by simp [wordA]
theorem wordB_len (l : List Edge) : (wordB l).length = l.length := by simp [wordB]
theorem wordC_len (l : List Edge) : (wordC l).length = l.length := by simp [wordC]

theorem valid_word {l : List Edge} (hl : ∀ e ∈ l, e ∈ edges) :
    Good l.length (marginal l) ∧
    (∀ a ∈ wordA l, A a) ∧ (∀ c ∈ wordC l, C c) ∧
    enc (wordA l) + enc (wordB l) + enc (wordC l) = cap l.length := by
  induction l with
  | nil => simp [Good,marginal,wordA,wordB,wordC,cap,enc,mass,weight]
  | cons e l ih =>
    obtain ⟨hg,ha,hc,hs⟩ := ih (fun f hf => hl f (by simp [hf]))
    have he := digitEdge e.1 e.2.1 e.2.2 (hl e (by simp))
    obtain ⟨hA,hC,hm,hw⟩ := he
    obtain ⟨hgm,hgw⟩ := hg
    simp only [Good,marginal] at hgm hgw ⊢
    simp only [wordA,wordB,wordC,List.map_cons,mass,weight,enc,List.length_cons,cap_succ] at *
    refine ⟨⟨by omega,by omega⟩,?_,?_,by omega⟩
    · intro a h; rcases List.mem_cons.mp h with rfl|h
      · exact hA
      · exact ha a h
    · intro c h; rcases List.mem_cons.mp h with rfl|h
      · exact hC
      · exact hc c h

theorem mass_bound (l : List Digit) : mass l ≤ 6*l.length := by
  induction l with
  | nil => decide
  | cons d ds ih => simp only [mass,List.length_cons]; have := d.isLt; omega

theorem u_bounds (l : List Digit) : 0 ≤ weight u l ∧ weight u l ≤ (l.length : Int) := by
  induction l with
  | nil => decide
  | cons d ds ih =>
    simp only [weight,u,List.length_cons]
    split <;> omega

theorem v_bounds (l : List Digit) : -(2*(l.length : Int)) ≤ weight v l ∧ weight v l ≤ 0 := by
  induction l with
  | nil => decide
  | cons d ds ih =>
    simp only [weight,v,List.length_cons]
    split <;> omega

theorem w_bounds (l : List Digit) : 0 ≤ weight w l ∧ weight w l ≤ 2*(l.length : Int) := by
  induction l with
  | nil => decide
  | cons d ds ih =>
    simp only [weight,w,List.length_cons]
    by_cases h : d = 5
    · simp [h]; omega
    · by_cases h' : d = 6 <;> simp [h,h'] <;> omega

def keys : List (List Edge → Nat) := [
  fun l => (marginal l).ma, fun l => (marginal l).mb, fun l => (marginal l).mc,
  fun l => (marginal l).wa.toNat, fun l => (-(marginal l).wb).toNat, fun l => (marginal l).wc.toNat]

theorem keys_bound {n : Nat} {l : List Edge} (hl : l ∈ allWords n) :
    ∀ f ∈ keys, f l < 6*n+1 := by
  intro f hf
  have hn := (words_props hl).1
  have ha := mass_bound (wordA l)
  have hb := mass_bound (wordB l)
  have hc := mass_bound (wordC l)
  have hwa := u_bounds (wordA l)
  have hwb := v_bounds (wordB l)
  have hwc := w_bounds (wordC l)
  rw [wordA_len,hn] at ha hwa
  rw [wordB_len,hn] at hb hwb
  rw [wordC_len,hn] at hc hwc
  simp [keys] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Nat.lt_succ_of_le ha
  · exact Nat.lt_succ_of_le hb
  · exact Nat.lt_succ_of_le hc
  · apply Nat.lt_succ_of_le; apply Int.toNat_le.mpr; simp only [marginal]; omega
  · apply Nat.lt_succ_of_le; apply Int.toNat_le.mpr; simp only [marginal]; omega
  · apply Nat.lt_succ_of_le; apply Int.toNat_le.mpr; simp only [marginal]; omega

theorem keys_determine {l r : List Edge} (h : ∀ f ∈ keys, f l = f r) : marginal l = marginal r := by
  have h1 := h (fun l => (marginal l).ma) (by simp [keys])
  have h2 := h (fun l => (marginal l).mb) (by simp [keys])
  have h3 := h (fun l => (marginal l).mc) (by simp [keys])
  have h4 := h (fun l => (marginal l).wa.toNat) (by simp [keys])
  have h5 := h (fun l => (-(marginal l).wb).toNat) (by simp [keys])
  have h6 := h (fun l => (marginal l).wc.toNat) (by simp [keys])
  have ha := (u_bounds (wordA l)).1
  have ha' := (u_bounds (wordA r)).1
  have hb := (v_bounds (wordB l)).2
  have hb' := (v_bounds (wordB r)).2
  have hc := (w_bounds (wordC l)).1
  have hc' := (w_bounds (wordC r)).1
  have hwa : (marginal l).wa = (marginal r).wa := by simp only [marginal] at h4 ⊢; omega
  have hwb : (marginal l).wb = (marginal r).wb := by simp only [marginal] at h5 ⊢; omega
  have hwc : (marginal l).wc = (marginal r).wc := by simp only [marginal] at h6 ⊢; omega
  cases hl : marginal l
  cases hr : marginal r
  simp_all


def toTarget (n : Nat) (l : List Edge) : Nat × Nat × Nat :=
  (enc (wordA l),enc (wordB l),shift (cap n) (enc (wordC l)))

theorem toTarget_mem {n : Nat} {s : Marginal} {l : List Edge} (hl : l ∈ allWords n)
    (hm : marginal l = s) : target n s (toTarget n l).1 (toTarget n l).2.1 (toTarget n l).2.2 := by
  obtain ⟨hlen,hall⟩ := words_props hl
  obtain ⟨hg,ha,hc,hs⟩ := valid_word hall
  have ba : enc (wordA l) ≤ cap n := by simpa [wordA_len,hlen] using enc_bound (wordA l)
  have bb : enc (wordB l) ≤ cap n := by simpa [wordB_len,hlen] using enc_bound (wordB l)
  have bc : enc (wordC l) ≤ cap n := by simpa [wordC_len,hlen] using enc_bound (wordC l)
  subst s
  refine ⟨by simp only [toTarget,modulus]; omega,by simp only [toTarget,modulus]; omega,
    shift_bound _ _,⟨wordA l,⟨by simp [wordA_len,hlen],ha,rfl,rfl⟩,rfl⟩,
    ⟨wordB l,⟨by simp [wordB_len,hlen],rfl,rfl⟩,rfl⟩,
    ⟨wordC l,⟨by simp [wordC_len,hlen],hc,rfl,rfl⟩,rfl⟩,?_⟩
  exact (shifted_sum ba bb bc).mpr (by simpa [hlen] using hs)

theorem word_components_inj {l r : List Edge} (ha : wordA l = wordA r)
    (hb : wordB l = wordB r) (hc : wordC l = wordC r) : l = r := by
  induction l generalizing r with
  | nil => cases r <;> simp_all [wordA]
  | cons e l ih =>
    cases r with
    | nil => simp [wordA] at ha
    | cons f r =>
      simp only [wordA,wordB,wordC,List.map_cons,List.cons.injEq] at ha hb hc
      have hef : e = f := by grind
      have htail : l = r := ih ha.2 hb.2 hc.2
      rw [hef,htail]

theorem toTarget_inj {n : Nat} {l r : List Edge} (hl : l ∈ allWords n) (hr : r ∈ allWords n)
    (h : toTarget n l = toTarget n r) : l = r := by
  have hll := (words_props hl).1
  have hrr := (words_props hr).1
  have ha := congrArg Prod.fst h
  have hb := congrArg (fun p => p.2.1) h
  have hc := congrArg (fun p => p.2.2) h
  simp only [toTarget] at ha hb hc
  have bl : enc (wordC l) ≤ cap n := by simpa [wordC_len,hll] using enc_bound (wordC l)
  have br : enc (wordC r) ≤ cap n := by simpa [wordC_len,hrr] using enc_bound (wordC r)
  have hcc := congrArg (unshift (cap n)) hc
  rw [unshift_shift bl,unshift_shift br] at hcc
  exact word_components_inj (enc_injective (by simp [wordA_len,hll,hrr]) ha)
    (enc_injective (by simp [wordB_len,hll,hrr]) hb)
    (enc_injective (by simp [wordC_len,hll,hrr]) hcc)

-- A lower bound on the number of distinct targets, for every radix length.
theorem large_cyclic (n : Nat) : ∃ s : Marginal, Good n s ∧
    ∃ ts : List (Nat × Nat × Nat), ts.Nodup ∧
    (∀ t ∈ ts, target n s t.1 t.2.1 t.2.2) ∧
    8^n ≤ (6*n+1)^6 * ts.length := by
  obtain ⟨b,hb,huniform,hcnt⟩ := many_buckets keys (6*n+1) (allWords n)
    (fun f hf l hl => keys_bound hl f hf)
  rw [words_length] at hcnt
  change 8^n ≤ (6*n+1)^6 * b.length at hcnt
  have hn : 0 < 8^n := Nat.pow_pos (by decide)
  cases hbb : b with
  | nil => rw [hbb] at hcnt; simp at hcnt
  | cons first rest =>
    have hfirst : first ∈ b := by simp [hbb]
    have hfirst' := hb.subset hfirst
    obtain ⟨hlen,hall⟩ := words_props hfirst'
    have hg : Good n (marginal first) := by simpa [hlen] using (valid_word hall).1
    let ts := b.map (toTarget n)
    refine ⟨marginal first,hg,ts,?_,?_,?_⟩
    · apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem (l := b) (R := fun a b => a ≠ b) _ ((words_nodup n).sublist hb)
      intro a c ha hc hne he
      exact hne (toTarget_inj (hb.subset ha) (hb.subset hc) he)
    · intro t ht
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp ht
      exact toTarget_mem (hb.subset hl) (keys_determine (fun f hf => huniform f hf l hl first hfirst))
    · simpa [ts] using hcnt


theorem linear_pow_bound (r : Nat) : 3000*r+1 ≤ 3001^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    have hp := Nat.mul_le_mul_right 3001 ih
    omega

theorem numeric_margin : 3001^6 * 7^506 ≤ 8^500 := by decide

theorem growth_at (r : Nat) : ∃ s : Marginal, Good (500*r) s ∧
    ∃ ts : List (Nat × Nat × Nat), ts.Nodup ∧
    (∀ t ∈ ts, target (500*r) s t.1 t.2.1 t.2.2) ∧
    7^(506*r) ≤ ts.length := by
  obtain ⟨s,hg,ts,hd,ht,hcnt⟩ := large_cyclic (500*r)
  refine ⟨s,hg,ts,hd,ht,?_⟩
  have he : 6*(500*r)+1 = 3000*r+1 := by omega
  rw [he] at hcnt
  have hpoly := Nat.pow_le_pow_left (linear_pow_bound r) 6
  have hb : (3000*r+1)^6 * 7^(506*r) ≤ 8^(500*r) := by
    calc
      (3000*r+1)^6 * 7^(506*r) ≤ (3001^r)^6 * 7^(506*r) := Nat.mul_le_mul_right _ hpoly
      _ = (3001^6 * 7^506)^r := by
        rw [← Nat.pow_mul, Nat.mul_comm r 6, Nat.pow_mul, Nat.pow_mul, ← Nat.mul_pow]
      _ ≤ (8^500)^r := Nat.pow_le_pow_left numeric_margin r
      _ = 8^(500*r) := (Nat.pow_mul _ _ _).symm
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans hb hcnt) (Nat.pow_pos (by omega))

theorem seven_pow_lower (r : Nat) : r+1 ≤ 7^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul_right 7 ih
    omega

theorem modulus_bounds (n : Nat) : 7^n ≤ modulus n ∧ modulus n ≤ 3*7^n := by
  have h := seven_pow_lower n
  simp only [modulus,cap]
  omega

-- A natural-number version of the exponent 1 + 1/q upper bound.
-- Distinct lists of targets are lower-bound certificates for the maximum val(Z_N).
def PrattBoundAt (q : Nat) : Prop :=
  ∃ K N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 0 < N →
    ∀ A B C : Nat → Prop, ETF (CyclicEdge N A B C) →
    ∀ ts : List (Nat × Nat × Nat), ts.Nodup →
    (∀ t ∈ ts, CyclicEdge N A B C t.1 t.2.1 t.2.2) →
    ts.length^q ≤ K*N^(q+1)

def PrattConjecture24 : Prop := ∀ q : Nat, 0 < q → PrattBoundAt q

-- Refute even the single exponent 1+1/100, with arbitrary K and threshold N₀.
theorem explicit_violation (K N₀ : Nat) :
    ∃ N : Nat, N₀ ≤ N ∧ 0 < N ∧
    ∃ A B C : Nat → Prop, ETF (CyclicEdge N A B C) ∧
    ∃ ts : List (Nat × Nat × Nat), ts.Nodup ∧
    (∀ t ∈ ts, CyclicEdge N A B C t.1 t.2.1 t.2.2) ∧
    K*N^101 < ts.length^100 := by
  let r := K*3^101+N₀+1
  let n := 500*r
  obtain ⟨s,hg,ts,hd,ht,hcnt⟩ := growth_at r
  let N := modulus n
  have hN := modulus_bounds n
  have hn := seven_pow_lower n
  have hr := seven_pow_lower r
  have hpos : 0 < N := by unfold N; omega
  have hthreshold : N₀ ≤ N := by
    have h₀ : N₀ ≤ r := by dsimp [r]; omega
    have h₁ : r ≤ n := by
      change r ≤ 500*r
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right r (by decide)
    exact Nat.le_trans h₀ (Nat.le_trans h₁ (Nat.le_trans (Nat.le_trans (Nat.le_succ n) hn) hN.1))
  have hsmall : K*3^101 < 7^(100*r) := by
    have h₀ : K*3^101 < r+1 := by dsimp [r]; omega
    have h₁ : r ≤ 100*r := by
      rw [Nat.mul_comm]
      exact Nat.le_mul_of_pos_right r (by decide)
    exact Nat.lt_of_lt_of_le h₀ (Nat.le_trans hr (Nat.pow_le_pow_right (by decide) h₁))
  have hp := Nat.pow_le_pow_left hN.2 101
  have hexp : 100*r+n*101 = 506*r*100 := by dsimp [n]; omega
  have hbig : K*N^101 < ts.length^100 := by
    calc
      K*N^101 ≤ K*(3*7^n)^101 := Nat.mul_le_mul_left _ hp
      _ = (K*3^101)*7^(n*101) := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.mul_assoc]
      _ < 7^(100*r)*7^(n*101) := Nat.mul_lt_mul_of_pos_right hsmall (Nat.pow_pos (by decide))
      _ = 7^(506*r*100) := by rw [← Nat.pow_add,hexp]
      _ = (7^(506*r))^100 := Nat.pow_mul _ _ _
      _ ≤ ts.length^100 := Nat.pow_le_pow_left hcnt _
  exact ⟨N,hthreshold,hpos,setA n s,setB n s,setC n s,targetETF hg,ts,hd,ht,hbig⟩

theorem not_PrattBoundAt_100 : ¬ PrattBoundAt 100 := by
  intro h
  obtain ⟨K,N₀,hbound⟩ := h
  obtain ⟨N,hN,hpos,A,B,C,hETF,ts,hd,ht,hbad⟩ := explicit_violation K N₀
  have hle := hbound N hN hpos A B C hETF ts hd ht
  exact (Nat.not_lt_of_ge hle) hbad

theorem not_PrattConjecture24 : ¬ PrattConjecture24 := by
  intro h
  exact not_PrattBoundAt_100 (h 100 (by decide))

#print axioms digitETF
#print axioms word_filter
#print axioms targetETF
#print axioms large_cyclic
#print axioms explicit_violation
#print axioms not_PrattConjecture24


-- The same theorem using the actual finite residue type and its addition.
def FinEdge (N : Nat) (P Q R : Fin N → Prop) (a b c : Fin N) : Prop :=
  P a ∧ Q b ∧ R c ∧ (a+b+c).val = 0

theorem fin_zero_equiv {N : Nat} [NeZero N] (a b c : Fin N) :
    (a+b+c).val = 0 ↔ a+b+c = 0 := by
  constructor
  · intro h; exact Fin.ext (by simpa using h)
  · intro h; rw [h,Fin.val_zero]

theorem fin_nat_edge {N : Nat} {P Q R : Nat → Prop} (a b c : Fin N) :
    FinEdge N (fun a => P a.val) (fun b => Q b.val) (fun c => R c.val) a b c ↔
    CyclicEdge N P Q R a.val b.val c.val := by
  simp [FinEdge,CyclicEdge,a.isLt,b.isLt,c.isLt,Fin.val_add,Nat.mod_add_mod]

theorem finETF_of_nat {N : Nat} {P Q R : Nat → Prop} (h : ETF (CyclicEdge N P Q R)) :
    ETF (FinEdge N (fun a => P a.val) (fun b => Q b.val) (fun c => R c.val)) := by
  constructor
  · intro a' b' a b c d e f h1 h2 h3 h4
    have e1 := (fin_nat_edge a' b c).mp h1
    have e2 := (fin_nat_edge a b' c).mp h2
    have e3 := (fin_nat_edge a' e f).mp h3
    have e4 := (fin_nat_edge d b' f).mp h4
    have he := h.1 a'.val b'.val _ _ _ _ _ _ e1 e2 e3 e4
    have ha : a = d := Fin.ext (congrArg Prod.fst he)
    have hb : b = e := Fin.ext (congrArg (fun p => p.2.1) he)
    have hc : c = f := Fin.ext (congrArg (fun p => p.2.2) he)
    rw [ha,hb,hc]
  constructor
  · intro a' c' a b c d e f h1 h2 h3 h4
    have e1 := (fin_nat_edge a' b c).mp h1
    have e2 := (fin_nat_edge a b c').mp h2
    have e3 := (fin_nat_edge a' e f).mp h3
    have e4 := (fin_nat_edge d e c').mp h4
    have he := h.2.1 a'.val c'.val _ _ _ _ _ _ e1 e2 e3 e4
    have ha : a = d := Fin.ext (congrArg Prod.fst he)
    have hb : b = e := Fin.ext (congrArg (fun p => p.2.1) he)
    have hc : c = f := Fin.ext (congrArg (fun p => p.2.2) he)
    rw [ha,hb,hc]
  · intro b' c' a b c d e f h1 h2 h3 h4
    have e1 := (fin_nat_edge a b' c).mp h1
    have e2 := (fin_nat_edge a b c').mp h2
    have e3 := (fin_nat_edge d b' f).mp h3
    have e4 := (fin_nat_edge d e c').mp h4
    have he := h.2.2 b'.val c'.val _ _ _ _ _ _ e1 e2 e3 e4
    have ha : a = d := Fin.ext (congrArg Prod.fst he)
    have hb : b = e := Fin.ext (congrArg (fun p => p.2.1) he)
    have hc : c = f := Fin.ext (congrArg (fun p => p.2.2) he)
    rw [ha,hb,hc]

def toFinTriple (N : Nat) [NeZero N] (t : Nat × Nat × Nat) : Fin N × Fin N × Fin N :=
  (Fin.ofNat N t.1, Fin.ofNat N t.2.1, Fin.ofNat N t.2.2)

def fromFinTriple {N : Nat} (t : Fin N × Fin N × Fin N) : Nat × Nat × Nat :=
  (t.1.val,t.2.1.val,t.2.2.val)

theorem fin_roundtrip {N : Nat} [NeZero N] {P Q R : Nat → Prop} {t : Nat × Nat × Nat}
    (ht : CyclicEdge N P Q R t.1 t.2.1 t.2.2) : fromFinTriple (toFinTriple N t) = t := by
  obtain ⟨ha,hb,hc,_,_,_,_⟩ := ht
  simp [toFinTriple,fromFinTriple,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem fin_witness_of_nat {N : Nat} {A B C : Nat → Prop} {ts : List (Nat × Nat × Nat)}
    (hpos : 0 < N) (hd : ts.Nodup) (ht : ∀ t ∈ ts, CyclicEdge N A B C t.1 t.2.1 t.2.2) :
    ∃ fs : List (Fin N × Fin N × Fin N), fs.Nodup ∧
      (∀ t ∈ fs, FinEdge N (fun a => A a.val) (fun b => B b.val) (fun c => C c.val) t.1 t.2.1 t.2.2) ∧
      fs.length = ts.length := by
  letI : NeZero N := ⟨by omega⟩
  let fs := ts.map (toFinTriple N)
  refine ⟨fs,?_,?_,by simp [fs]⟩
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (l := ts) (R := fun a b => a ≠ b) _ hd
    intro a b ha hb hne he
    apply hne
    have he' := congrArg fromFinTriple he
    rw [fin_roundtrip (ht a ha),fin_roundtrip (ht b hb)] at he'
    exact he'
  · intro t hmem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hmem
    apply (fin_nat_edge _ _ _).mpr
    have hv' := ht v hv
    have hrt := fin_roundtrip hv'
    have hh := hv'
    rw [← hrt] at hh
    exact hh

theorem fin_explicit_violation (K N₀ : Nat) :
    ∃ N : Nat, N₀ ≤ N ∧ 0 < N ∧
    ∃ A B C : Fin N → Prop, ETF (FinEdge N A B C) ∧
    ∃ ts : List (Fin N × Fin N × Fin N), ts.Nodup ∧
    (∀ t ∈ ts, FinEdge N A B C t.1 t.2.1 t.2.2) ∧
    K*N^101 < ts.length^100 := by
  obtain ⟨N,hN,hpos,A,B,C,hETF,ts,hd,ht,hbad⟩ := explicit_violation K N₀
  obtain ⟨fs,hfd,hft,hfl⟩ := fin_witness_of_nat hpos hd ht
  exact ⟨N,hN,hpos,fun a => A a.val,fun b => B b.val,fun c => C c.val,
    finETF_of_nat hETF,fs,hfd,hft,by rw [hfl]; exact hbad⟩

def FinPrattBoundAt (q : Nat) : Prop :=
  ∃ K N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 0 < N →
    ∀ A B C : Fin N → Prop, ETF (FinEdge N A B C) →
    ∀ ts : List (Fin N × Fin N × Fin N), ts.Nodup →
    (∀ t ∈ ts, FinEdge N A B C t.1 t.2.1 t.2.2) →
    ts.length^q ≤ K*N^(q+1)

def FinPrattConjecture24 : Prop := ∀ q : Nat, 0 < q → FinPrattBoundAt q

theorem not_FinPrattConjecture24 : ¬ FinPrattConjecture24 := by
  intro h
  obtain ⟨K,N₀,hbound⟩ := h 100 (by decide)
  obtain ⟨N,hN,hpos,A,B,C,hETF,ts,hd,ht,hbad⟩ := fin_explicit_violation K N₀
  exact (Nat.not_lt_of_ge (hbound N hN hpos A B C hETF ts hd ht)) hbad

#print axioms fin_explicit_violation
#print axioms not_FinPrattConjecture24


-- A literal finite maximum for val(Z_N), independently of the witness-list formulation.
def cart {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x,y)))

theorem mem_cart {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β} :
    (x,y) ∈ cart xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [cart,List.mem_flatMap,List.mem_map]

theorem cart_nodup {α β : Type} (xs : List α) (ys : List β)
    (hx : xs.Nodup) (hy : ys.Nodup) : (cart xs ys).Nodup := by
  induction xs with
  | nil => simp [cart]
  | cons x xs ih =>
    obtain ⟨hn,hxs⟩ := List.nodup_cons.mp hx
    simp only [cart,List.flatMap_cons] at ⊢
    rw [List.nodup_append]
    refine ⟨List.pairwise_map.mpr (hy.imp (fun h he => h (congrArg Prod.snd he))),ih hxs,?_⟩
    intro a ha b hb he
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨z,hz,hzm⟩ := List.mem_flatMap.mp hb
    obtain ⟨y',_,rfl⟩ := List.mem_map.mp hzm
    have hxz : x = z := congrArg Prod.fst he
    exact hn (hxz.symm ▸ hz)

def allFinTriples (N : Nat) : List (Fin N × Fin N × Fin N) :=
  cart (List.finRange N) (cart (List.finRange N) (List.finRange N))

theorem allFinTriples_complete {N : Nat} (t : Fin N × Fin N × Fin N) : t ∈ allFinTriples N := by
  rcases t with ⟨a,b,c⟩
  simp [allFinTriples,mem_cart,List.mem_finRange]

theorem allFinTriples_nodup (N : Nat) : (allFinTriples N).Nodup :=
  cart_nodup _ _ (List.nodup_finRange _) (cart_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))

noncomputable def targetList (N : Nat) (P Q R : Fin N → Prop) : List (Fin N × Fin N × Fin N) := by
  classical
  exact (allFinTriples N).filter (fun t => decide (FinEdge N P Q R t.1 t.2.1 t.2.2))

theorem targetList_mem {N : Nat} {P Q R : Fin N → Prop} (t : Fin N × Fin N × Fin N) :
    t ∈ targetList N P Q R ↔ FinEdge N P Q R t.1 t.2.1 t.2.2 := by
  classical
  simp [targetList,allFinTriples_complete]

theorem targetList_nodup (N : Nat) (P Q R : Fin N → Prop) : (targetList N P Q R).Nodup := by
  classical
  unfold targetList
  exact (allFinTriples_nodup N).filter _

noncomputable def targetCount (N : Nat) (P Q R : Fin N → Prop) : Nat :=
  (targetList N P Q R).length

theorem count_ge_witness {N : Nat} {P Q R : Fin N → Prop} {ts : List (Fin N × Fin N × Fin N)}
    (hd : ts.Nodup) (ht : ∀ t ∈ ts, FinEdge N P Q R t.1 t.2.1 t.2.2) : ts.length ≤ targetCount N P Q R :=
  hd.length_le_of_subset (fun t h => (targetList_mem t).mpr (ht t h))

def powerset {α : Type} : List α → List (List α)
  | [] => [[]]
  | x::xs => powerset xs ++ (powerset xs).map (fun l => x::l)

theorem filter_in_powerset {α : Type} (p : α → Bool) (xs : List α) : xs.filter p ∈ powerset xs := by
  induction xs with
  | nil => simp [powerset]
  | cons x xs ih =>
    simp only [powerset,List.filter_cons,List.mem_append]
    by_cases h : p x = true
    · simp only [h, ite_true]
      exact Or.inr (List.mem_map.mpr ⟨xs.filter p,ih,rfl⟩)
    · simp only [h]
      exact Or.inl ih

noncomputable def candidateValue (N : Nat) (t : List (Fin N) × List (Fin N) × List (Fin N)) : Nat := by
  classical
  let P : Fin N → Prop := fun a => a ∈ t.1
  let Q : Fin N → Prop := fun b => b ∈ t.2.1
  let R : Fin N → Prop := fun c => c ∈ t.2.2
  exact if ETF (FinEdge N P Q R) then targetCount N P Q R else 0

noncomputable def val (N : Nat) : Nat :=
  let ps := powerset (List.finRange N)
  ((cart ps (cart ps ps)).map (candidateValue N)).foldl max 0

theorem foldmax_ge_init (xs : List Nat) (m : Nat) : m ≤ xs.foldl max m := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldmax_ge_mem {xs : List Nat} {x : Nat} (hx : x ∈ xs) (m : Nat) : x ≤ xs.foldl max m := by
  induction xs generalizing m with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldmax_ge_init _ _)
    · exact ih hx _

theorem val_ge_count {N : Nat} {P Q R : Fin N → Prop} (h : ETF (FinEdge N P Q R)) :
    targetCount N P Q R ≤ val N := by
  classical
  let as := (List.finRange N).filter (fun a => decide (P a))
  let bs := (List.finRange N).filter (fun b => decide (Q b))
  let cs := (List.finRange N).filter (fun c => decide (R c))
  have ha : (fun a => a ∈ as) = P := by funext a; apply propext; simp [as,List.mem_finRange]
  have hb : (fun b => b ∈ bs) = Q := by funext b; apply propext; simp [bs,List.mem_finRange]
  have hc : (fun c => c ∈ cs) = R := by funext c; apply propext; simp [cs,List.mem_finRange]
  have hval : candidateValue N (as,bs,cs) = targetCount N P Q R := by
    unfold candidateValue
    dsimp only
    rw [ha,hb,hc]
    simp [h]
  have hm : (as,bs,cs) ∈ cart (powerset (List.finRange N))
      (cart (powerset (List.finRange N)) (powerset (List.finRange N))) := by
    exact mem_cart.mpr ⟨filter_in_powerset _ _,mem_cart.mpr ⟨filter_in_powerset _ _,filter_in_powerset _ _⟩⟩
  unfold val
  apply foldmax_ge_mem _ 0
  exact List.mem_map.mpr ⟨(as,bs,cs),hm,hval⟩


theorem foldmax_le {xs : List Nat} {m bound : Nat} (hm : m ≤ bound)
    (hx : ∀ x ∈ xs, x ≤ bound) : xs.foldl max m ≤ bound := by
  induction xs generalizing m with
  | nil => exact hm
  | cons x xs ih =>
    exact ih (Nat.max_le.mpr ⟨hm,hx x (by simp)⟩) (fun y hy => hx y (by simp [hy]))

-- This establishes that the finite maximum is exactly the value in Definition 17.
theorem val_le_iff (N bound : Nat) : val N ≤ bound ↔
    ∀ P Q R : Fin N → Prop, ETF (FinEdge N P Q R) → targetCount N P Q R ≤ bound := by
  constructor
  · intro h P Q R hETF
    exact Nat.le_trans (val_ge_count hETF) h
  · intro h
    classical
    unfold val
    apply foldmax_le (by omega)
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    unfold candidateValue
    dsimp only
    split
    · rename_i hETF
      exact h _ _ _ hETF
    · omega

-- The all-length lower bound directly for the finite maximum val.
theorem val_lower (n : Nat) : 8^n ≤ (6*n+1)^6 * val (modulus n) := by
  obtain ⟨s,hg,ts,hd,ht,hcnt⟩ := large_cyclic n
  have hpos : 0 < modulus n := by unfold modulus; omega
  obtain ⟨fs,hfd,hft,hfl⟩ := fin_witness_of_nat hpos hd ht
  have hETF := finETF_of_nat (targetETF hg)
  have hval := Nat.le_trans (count_ge_witness hfd hft) (val_ge_count hETF)
  rw [← hfl] at hcnt
  exact Nat.le_trans hcnt (Nat.mul_le_mul_left _ hval)

#print axioms val_le_iff
#print axioms val_lower

-- Original asymptotic upper bound in the necessary rational-exponent form.
def ValPrattConjecture24 : Prop := ∀ q : Nat, 0 < q →
  ∃ K N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 0 < N → (val N)^q ≤ K*N^(q+1)

theorem not_ValPrattConjecture24 : ¬ ValPrattConjecture24 := by
  intro h
  obtain ⟨K,N₀,hbound⟩ := h 100 (by decide)
  obtain ⟨N,hN,hpos,A,B,C,hETF,ts,hd,ht,hbad⟩ := fin_explicit_violation K N₀
  have hval := Nat.le_trans (count_ge_witness hd ht) (val_ge_count hETF)
  have hpow := Nat.pow_le_pow_left hval 100
  exact (Nat.not_lt_of_ge (Nat.le_trans hpow (hbound N hN hpos))) hbad

#print axioms val_ge_count
#print axioms not_ValPrattConjecture24

end Pratt
