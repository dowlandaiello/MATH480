import Mathlib.Tactic
inductive Round where
  | prepare  : Round
  | promise  : Round
  | accept   : Round
  | accepted : Round
deriving Repr

inductive Message where
  | prepare               : ℕ → Message
  | promise_prev_accepted : ℕ → ℕ → Message

structure AddressedMessage (ntotalnodes : ℕ) where
  cts    : Message
  recip  : Fin ntotalnodes
  sender : Fin ntotalnodes


class Agent (ntotalnodes : ℕ) (α : Type) where
  process : α → AddressedMessage n → (Option $ AddressedMessage ntotalnodes)
  advance : α → α × (List $ AddressedMessage ntotalnodes)

inductive PState (α : Type) where
  | error : PState α
  | val   : α → PState α

structure Proposer (α : Type) where
  acceptors : List ℕ
  proposal  : α

structure Acceptor (ntotalnodes : ℕ) where
  queue      : List $ AddressedMessage ntotalnodes
  max_msg_id : ℕ
  id         : Fin ntotalnodes

def process (ntotalnodes : ℕ) (a : Acceptor ntotalnodes) (x : AddressedMessage ntotalnodes) : Option $ AddressedMessage ntotalnodes :=
  match x.cts with
    | Message.prepare n =>
      let prev := a.max_msg_id
      pure $ ⟨Message.promise_prev_accepted prev n, a.id, x.sender⟩
    | Message.promise_prev_accepted _ _ => none

def advance (ntotalnodes : ℕ) (a : Acceptor ntotalnodes) : Acceptor ntotalnodes × (List $ AddressedMessage ntotalnodes) :=
  List.foldl (fun ⟨a, ret_msgs⟩ msg => match process ntotalnodes a msg with
    | none => ⟨a, ret_msgs⟩
    | some m@⟨(Message.promise_prev_accepted _ accepted), _, _⟩ => ⟨{ a with max_msg_id := accepted }, ret_msgs ++ [m]⟩
    | some x => ⟨a, ret_msgs ++ [x]⟩
  ) ⟨a, List.nil⟩ a.queue

def process (ntotalnodes : ℕ) (p : Proposer ntotalnodes) (x : AddressedMessage ntotalnodes) : Option $ AddressedMessage ntotalnodes := sorry

def Quorum (ntotalnodes : ℕ) := Vector ℕ (ntotalnodes / 2)

def MsgQueue (ntotalnodes : ℕ) := List $ AddressedMessage ntotalnodes

def send (n : ℕ) : AddressedMessage n → MsgQueue n → MsgQueue n := (. :: .)


