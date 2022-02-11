{- What do we need? 
    - target ... this is who send the proposal. This will eventually have type place. 
    - appraiser ... who sends request. This will also have type place. 
    - privacy policy ... assume now that nothing violates privacy policy 
    - selection policy ... assume now that the longest measurement is the best -}

    
{- for now, possible protocols include copying, signing, hashing. 
   to make a more complex TERM type, check out `Term_Defs.hs in /haskell-am/copland-interp/extracted_src/Term_Defs.hs-}
data Protocol = 
      CPY
    | SIG 
    | HSH
    deriving (Show)

data Negotiate = Negotiate {  request :: Protocol
                            , proposal :: [Protocol]
                            , choosen_protocol :: Maybe Protocol }



{- this negotiation function will be the negotiation of the target's side. 

    things we could do: 
    - could make a map of request to possible protocols? 
    -}
neg_t :: request -> [Protocol]
neg_t r = 
    case r of {
        _ -> [HSH]
    }

neg_a :: [Protocol] -> Maybe Protocol
neg_a p = case p of 
    [] -> Nothing 
    (x:_) -> Just x 

{- Now to combine into one negotiate function -}

negotiate :: request -> Maybe Protocol
negotiate r = 
    let proposal = neg_t r
        prot = neg_a proposal
    in prot